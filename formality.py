class Context:
    def __init__(self, list = []):
        self.list = list

    def shift(self, depth, inc):
        new_list = []
        for binder in self.list:
            if binder is None:
                new_list.append(None)
            else:
                new_list.append((binder[0], binder[1].shift(depth, inc)))
        return Context(new_list)

    def extend(self, (name, term)):
        return Context([(name, term.shift(0, 1) if term else Var(0))] + self.shift(0, 1).list)

    def get_type(self, index):
        if index < len(self.list):
            return self.list[index][1]

    def get_name(self, index):
        if index < len(self.list):
            name = self.list[index][0]
            for i in xrange(index):
                if self.list[i][0] == self.list[index][0]:
                    name += "'"
            return name

    def find_by_name(self, name, skip):
        for i in xrange(len(self.list)):
            if self.list[i][0] == name:
                if skip == 0:
                    return self.list[i]
                else:
                    skip = skip - 1
        return None

class Typ:
    def __init__(self):
        pass

    def to_string(self, context):
        return "Type"

    def shift(self, depth, inc):
        return Typ()

    def subst(self, depth, val):
        return Typ()

    def uses(self, depth):
        return 0

    def equal(self, other):
        return isinstance(other, Typ)

    def eval(self, eras):
        return Typ()

    def check(self, context):
        return Typ()

class All:
    def __init__(self, eras, name, bind, body):
        self.eras = eras
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        return "{" + ("-" if self.eras else "") + self.name + " : " + self.bind.to_string(context) + "} " + self.body.to_string(context.extend((self.name, self.bind)))

    def shift(self, depth, inc):
        return All(self.eras, self.name, self.bind.shift(depth, inc), self.body.shift(depth + 1, inc))

    def subst(self, depth, val):
        return All(self.eras, self.name, self.bind.subst(depth, val), self.body.subst(depth + 1, val and val.shift(0, 1)))

    def uses(self, depth):
        return self.bind.uses(depth) + self.body.uses(depth + 1)

    def equal(self, other):
        return isinstance(other, All) and self.eras == other.eras and self.bind.equal(other.bind) and self.body.equal(other.body)

    def eval(self, eras):
        return All(self.eras, self.name, self.bind.eval(eras), self.body.eval(eras))

    def check(self, context):
        bind_v = self.bind
        bind_t = self.bind.check(context)
        body_t = self.body.check(context.extend((self.name, bind_v)))
        if not bind_t.eval(True).equal(Typ()) or not body_t.eval(True).equal(Typ()):
            raise(Exception("Forall not a type."))
        return Typ()

class Lam:
    def __init__(self, eras, name, bind, body):
        self.eras = eras
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        if self.bind is None:
            return "[" + self.name + "] " + self.body.to_string(context.extend((self.name, None)))
        else:
            return "[" + ("-" if self.eras else "") + self.name + " : " + self.bind.to_string(context) + "] " + self.body.to_string(context.extend((self.name, self.bind)))

    def shift(self, depth, inc):
        return Lam(self.eras, self.name, self.bind and self.bind.shift(depth, inc), self.body.shift(depth + 1, inc))

    def subst(self, depth, val):
        return Lam(self.eras, self.name, self.bind and self.bind.subst(depth, val), self.body.subst(depth + 1, val and val.shift(0, 1)))

    def uses(self, depth):
        return self.bind.uses(depth) + self.body.uses(depth + 1)

    def equal(self, other):
        return isinstance(other, Lam) and self.eras == other.eras and self.body.equal(other.body)

    def eval(self, eras):
        if eras and self.eras:
            return self.body.eval(eras).subst(0, None)
        else:
            return Lam(self.eras, self.name, None if eras else self.bind.eval(eras), self.body.eval(eras))

    def check(self, context):
        if self.bind is None:
            raise(Exception("Can't infer non-annotated lambda."))
        else:
            bind_v = self.bind
            bind_t = self.bind.check(context)
            body_t = self.body.check(context.extend((self.name, bind_v)))
            if not bind_t.eval(True).equal(Typ()):
                raise(Exception("Function type not a type."))
            return All(self.eras, self.name, bind_v, body_t)

class App:
    def __init__(self, eras, func, argm):
        self.eras = eras
        self.func = func
        self.argm = argm

    def to_string(self, context):
        return "(" + self.func.to_string(context) + " " + ("-" if self.eras else "") + self.argm.to_string(context) + ")"

    def shift(self, depth, inc):
        return App(self.eras, self.func.shift(depth, inc), self.argm.shift(depth, inc))

    def subst(self, depth, val):
        return App(self.eras, self.func.subst(depth, val), self.argm.subst(depth, val))

    def uses(self, depth):
        return self.func.uses(depth) + self.argm.uses(depth)

    def equal(self, other):
        return isinstance(other, App) and self.eras == other.eras and self.func.equal(other.func) and self.argm.equal(other.argm)

    def eval(self, eras):
        if eras and self.eras:
            return self.func.eval(eras)
        else:
            func_v = self.func.eval(eras)
            if not isinstance(func_v, Lam):
                return App(self.eras, func_v, self.argm.eval(eras))
            return func_v.body.subst(0, self.argm).eval(eras)

    def check(self, context):
        func_t = self.func.check(context)
        argm_t = self.argm.check(context)
        if not isinstance(func_t.eval(True), All):
            raise(Exception("Non-function application: " + self.to_string(context)))
        if func_t.eval(True).eras != self.eras:
            raise(Exception("Erasure doesn't match on application: " + self.to_string(context)))
        if not func_t.eval(True).bind.equal(argm_t.eval(True)):
            raise(Exception("Type mismatch on '" + self.to_string(context) + "' application.\n"
                + "- Expect : " + func_t.bind.eval(True).to_string(Context()) + "\n"
                + "- Actual : " + argm_t.eval(True).to_string(Context())))
        return func_t.eval(False).body.subst(0, self.argm)

class Var:
    def __init__(self, index):
        self.index = index

    def to_string(self, context):
        return context.get_name(self.index) or "#" + str(self.index)

    def shift(self, depth, inc):
        return Var(self.index if self.index < depth else self.index + inc)

    def subst(self, depth, val):
        if depth == self.index:
            if val is None:
                #return Typ()
                raise(Exception("Use of erased variable."))
            else:
                return val
        return Var(self.index - (1 if self.index > depth else 0))

    def uses(self, depth):
        return 1 if depth == self.index else 0

    def equal(self, other):
        return isinstance(other, Var) and self.index == other.index

    def eval(self, eras):
        return Var(self.index)

    def check(self, context):
        return context.get_type(self.index)

class Dat:
    def __init__(self):
        pass

    def to_string(self, context):
        return "Data"

    def shift(self, depth, inc):
        return Dat()

    def subst(self, depth, val):
        return Dat()

    def uses(self, depth):
        return 0

    def equal(self, other):
        return isinstance(other, Dat)

    def eval(self, eras):
        return Dat()

    def check(self, context):
        return Typ()

class Idt:
    def __init__(self, name, type, ctrs):
        self.name = name # string
        self.type = type # term
        self.ctrs = ctrs # [(string, term)]

    def to_string(self, context):
        result = "<" + self.name + " : " + self.type.to_string(context)
        for (i, (name, type)) in enumerate(self.ctrs):
            result += " | " + name + " : " + type.to_string(context.extend((self.name, self.type)))
        return result + ">"

    def shift(self, depth, inc):
        return Idt(self.name, self.type.shift(depth, inc), [(name, type.shift(depth + 1, inc)) for (name, type) in self.ctrs])

    def subst(self, depth, val):
        return Idt(self.name, self.type.subst(depth, val), [(name, type.subst(depth + 1, val.shift(0, 1))) for (name, type) in self.ctrs])

    def uses(self, depth):
        return self.type.uses(depth) + sum([type.uses(depth + 1) for (_, type) in self.ctrs])

    def equal(self, other):
        return isinstance(other, Idt) and self.type.equal(other.type) and all([a[1].equal(b[1]) for (a,b) in zip(self.ctrs, other.ctrs)])

    def eval(self, eras):
        return Idt(self.name, self.type.eval(eras), [(name, type.eval(eras)) for (name, type) in self.ctrs])

    def check(self, context):
        return Dat()

    def get_vars(self):
        type_vars = []
        self_type = self.type
        while isinstance(self_type, All):
            type_vars.append(self_type.name)
            self_type = self_type.body
        ctrs_vars = []
        for (ctr_name, ctr_type) in self.ctrs:
            ctr_vars = []
            while isinstance(ctr_type, All):
                ctr_vars.append(ctr_type.name)
                ctr_type = ctr_type.body
            ctrs_vars.append((ctr_name, ctr_vars))
        return (type_vars, ctrs_vars)

    def derive_type(self):
        def build_indices(depth, indices_type):
            if isinstance(indices_type, All):
                return Lam(indices_type.eras, indices_type.name, indices_type.bind, build_indices(depth + 1, indices_type.body))
            else:
                return build_motive(depth)

        def build_motive(depth):
            return All(True, self.name, self.type.shift(0, depth), build_constructor(depth + 1, 0))

        def build_constructor(depth, num):
            if num < len(self.ctrs):
                (name, type) = self.ctrs[num]
                return All(False, name, type.shift(1, depth).subst(0, Var(num)), build_constructor(depth + 1, num + 1))
            else:
                return build_return_type(depth, self.type, 0, Var(len(self.ctrs)))

        def build_return_type(depth, indices_type, index, return_type):
            if isinstance(indices_type, All):
                return build_return_type(depth, indices_type.body, index + 1, App(indices_type.eras, return_type, Var(depth - index - 1)))
            else:
                return return_type

        return build_indices(0, self.type)

    def derive_constructor(self, name):
        for (ctr_index, (ctr_name, ctr_type)) in enumerate(self.ctrs):
            if name == ctr_name:
                break

        def build_lambdas(depth, fields_type):
            if isinstance(fields_type, All):
                return Lam(fields_type.eras, fields_type.name, fields_type.bind, build_lambdas(depth + 1, fields_type.body))
            else:
                return build_body(depth, ctr_type, 0, Var(len(self.ctrs) - ctr_index - 1))
                #return build_lambda_headers(depth, build_idt_type(fields_type))

        def build_body(depth, fields_type, field_index, term):
            if isinstance(fields_type, All):
                field = Var(depth - field_index - 1)
                # TODO: currently only works for very simple recursive ocurrences
                if fields_type.bind.uses(field_index) > 0:
                    field = App(True, field, Var(len(self.ctrs)))
                    for i in xrange(len(self.ctrs)):
                        field = App(False, field, Var(len(self.ctrs) - i - 1))
                return build_body(depth, fields_type.body, field_index + 1, App(fields_type.eras, term, field))
            else:
                return term

        return build_lambdas(0, ctr_type.subst(0, self.derive_type()).eval(False))

    def to_inductive(self):
        def build_motive(depth, motive_type, self_type):
            if isinstance(motive_type, All):
                return All(motive_type.eras, motive_type.name, motive_type.bind, build_motive(depth + 1, motive_type.body, App(motive_type.eras, self_type.shift(0, 1), Var(0))))
            else:
                return All(False, "self", self_type, motive_type)

        def build_constructor(depth, fields_type, self_value):
            if isinstance(fields_type, All):
                # TODO: currently only works for very simple recursive ocurrences
                if fields_type.bind.uses(depth) > 0:
                    body = build_constructor(depth + 2, fields_type.body.shift(0, 1), App(fields_type.eras, self_value.shift(0, 2), Var(1)))
                    all1 = All(fields_type.eras, fields_type.name, App(False, fields_type.bind.shift(0, 1), Var(0)), body)
                    all0 = All(True, fields_type.name + "_index", fields_type.bind.subst(depth, self.derive_type().shift(0, depth)), all1)
                    return all0
                else:
                    body = build_constructor(depth + 1, fields_type.body, App(fields_type.eras, self_value.shift(0, 1), Var(0)))
                    all0 = All(fields_type.eras, fields_type.name, fields_type.bind, body)
                    return all0
            else:
                return App(False, fields_type, self_value)
        
        moti = build_motive(0, self.type, self.derive_type())
        ctrs = [(ctr_name, build_constructor(0, ctr_type, self.derive_constructor(ctr_name))) for (ctr_name, ctr_type) in self.ctrs]
        return Idt(self.name + "_ind", moti, ctrs).eval(False)

class Ity:
    def __init__(self, data):
        self.data = data

    def to_string(self, context):
        return "!" + self.data.to_string(context)

    def shift(self, depth, inc):
        return Ity(self.data.shift(depth, inc))

    def subst(self, depth, val):
        return Ity(self.data.subst(depth, val))

    def uses(self, depth):
        return self.data.uses(depth)

    def equal(self, other):
        return isinstance(other, Ity) and self.data.equal(other.data)

    def eval(self, eras):
        data_v = self.data
        if isinstance(data_v, Idt):
            return data_v.derive_type().eval(eras)
        else:
            return Ity(data_v)

    def check(self, context):
        data_v = self.data
        if isinstance(data_v, Idt):
            return data_v.derive_type().check(context).eval(False)
        else:
            raise(Exception("Couldn't determine datatype statically: " + self.to_string(context)))

class Con:
    def __init__(self, data, name):
        self.data = data
        self.name = name

    def to_string(self, context):
        return "@" + self.data.to_string(context) + "." + self.name

    def shift(self, depth, inc):
        return Con(self.data.shift(depth, inc), self.name)

    def subst(self, depth, val):
        return Con(self.data.subst(depth, val), self.name)

    def uses(self, depth):
        return self.data.uses(depth)

    def equal(self, other):
        return isinstance(other, Con) and self.data.equal(other.data) and self.name == other.name

    def eval(self, eras):
        data_v = self.data
        if isinstance(data_v, Idt):
            return data_v.derive_constructor(self.name).eval(eras)
        else:
            return Con(data_v, self.name)

    def check(self, context):
        data_v = self.data
        if isinstance(data_v, Idt):
            return data_v.derive_constructor(self.name).check(context).eval(False)
        else:
            raise(Exception("Couldn't determine datatype statically: " + self.to_string(context)))

class Ind:
    def __init__(self, data, term, moti, cses):
        self.data = data
        self.term = term
        self.moti = moti
        self.cses = cses

    def to_string(self, context):
        vars = self.data.to_inductive().get_vars()
        text = "? " + self.data.to_string(context)
        text += " " + self.term.to_string(context) + " ->"
        text += " " + self.moti.to_string(reduce(lambda ctx, var: ctx.extend((var, None)), vars[0], context))
        for (i, (ctr_name, ctr_vars)) in enumerate(vars[1]):
            text += " | " + ctr_name + " => " + self.cses[i].to_string(reduce(lambda ctx, var: ctx.extend((var, None)), ctr_vars, context))
        return text + " ;"

    def get_indices(self, context):
        def extract(depth, term_type):
            if isinstance(term_type, All):
                return extract(depth + 1, term_type.body)
            if isinstance(term_type, App):
                return extract(depth, term_type.func) + [term_type.argm.shift(0, -depth)]
            return []
        return extract(0, self.term.check(context))

    def build(self):
        def build_term(type, body, vars):
            if vars > 0:
                return Lam(type.eras, type.name, type.bind, build_term(type.body, body, vars - 1))
            else:
                return body
        indu = self.data.to_inductive()
        vars = indu.get_vars()
        moti = build_term(indu.type, self.moti, len(vars[0]))
        cses = []
        for (ctr_index, ((ctr_name, ctr_type), ctr_body)) in enumerate(zip(indu.ctrs, self.cses)):
            ctr_type = ctr_type.subst(0, moti).eval(False)
            ctr_term = build_term(ctr_type, ctr_body, len(vars[1][ctr_index][1]))
            cses.append((ctr_name, ctr_term, ctr_type))
        return (moti, cses)

    def shift(self, depth, inc):
        vars = self.data.to_inductive().get_vars()
        data = self.data.shift(depth, inc)
        term = self.term.shift(depth, inc)
        moti = self.moti.shift(depth + len(vars[0]), inc)
        ctrs = [self.cses[i].shift(depth + len(vars[1][i]), inc) for i in xrange(len(self.cses))]
        return Ind(data, term, moti, ctrs)

    def subst(self, depth, val):
        vars = self.data.to_inductive().get_vars()
        data = self.data.subst(depth, val)
        term = self.term.subst(depth, val)
        moti = self.moti.subst(depth + len(vars[0]), val)
        ctrs = [self.cses[i].subst(depth + len(vars[1][i]), val) for i in xrange(len(self.cses))]
        return Ind(data, term, moti, ctrs)

    def uses(self, depth):
        vars = self.data.to_inductive().get_vars()
        data = self.data.uses(depth)
        term = self.term.uses(depth)
        moti = self.moti.uses(depth + len(vars[0]))
        ctrs = sum([self.cses[i].uses(depth + len(vars[1][i])) for i in xrange(len(self.cses))])
        return data + term + moti + ctrs

    def equal(self, other):
        data = self.data.equal(other.data)
        term = self.term.equal(other.term)
        moti = self.moti.equal(other.moti)
        ctrs = all([a.equal(b) for (a,b) in zip(self.ctrs, other.ctrs)])
        return data and term and moti and ctrs

    def eval(self, eras):
        if not eras:
            data = self.data.eval(eras)
            term = self.term.eval(eras)
            moti = self.moti.eval(eras)
            ctrs = [self.cses[i].eval(eras) for i in xrange(len(self.cses))]
            return Ind(data, term, moti, ctrs)
        else:
            (moti, cses) = self.build()
            term = App(True, self.term, moti)
            for (cse_name, cse_term, cse_type) in cses:
                term = App(False, term, cse_term)
            return term.eval(eras)

    def check(self, context):
        # TODO: check type of self.term
        (moti, cses) = self.build()
        for (cse_name, cse_term, cse_type) in cses:
            expect = cse_type
            actual = cse_term.check(context)
            if not expect.eval(True).equal(actual.eval(True)):
                raise(Exception("Type mismatch on '" + cse_name + "' case:\n"
                    + "- Expect : " + expect.eval(True).to_string(context) + "\n"
                    + "- Actual : " + actual.eval(True).to_string(context)))
        result = moti.eval(False)
        for idx in self.get_indices(context):
            result = result.body.subst(0, idx)
        result = result.body.subst(0, self.term)
        return result

def string_to_term(code):
    class Cursor:
        index = 0

    def is_space(char):
        return char in " \t\n"

    def is_name_char(char):
        return char in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"

    def skip_spaces():
        while Cursor.index < len(code) and is_space(code[Cursor.index]):
            Cursor.index += 1
        return Cursor.index

    def match(string):
        skip_spaces()
        sliced = code[Cursor.index : Cursor.index + len(string)]
        if sliced == string:
            Cursor.index += len(string)
            return True
        return False

    def parse_exact(string):
        if not match(string):
            raise(Exception("Parse error, expected '" + str(string) + "' at index " + str(Cursor.index) + "."))
        
    def parse_name():
        skip_spaces()
        name = ""
        while Cursor.index < len(code) and is_name_char(code[Cursor.index]):
            name = name + code[Cursor.index]
            Cursor.index += 1
        return name
        
    def parse_term(context):
        # Comment
        if match("--"):
            while Cursor.index < len(code) and code[Cursor.index] != "\n":
                Cursor.index += 1
            return parse_term(context)

        # Application
        elif match("("):
            func = parse_term(context)
            while Cursor.index < len(code) and not match(")"):
                eras = match("-")
                argm = parse_term(context)
                func = App(eras, func, argm)
                skip_spaces()
            return func

        # Type
        elif match("Type"):
            return Typ()

        # Forall
        elif match("{"):
            eras = match("-")
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context)
            skip = parse_exact("}")
            body = parse_term(context.extend((name, None)))
            return All(eras, name, bind, body)

        # Lambda
        elif match("["):
            eras = match("-")
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context)
            skip = parse_exact("]")
            body = parse_term(context.extend((name, None)))
            return Lam(eras, name, bind, body)

        # Definition
        elif match("def"):
            name = parse_name()
            term = parse_term(context)
            body = parse_term(context.extend((name, term)))
            return body

        # Data
        elif match("Data"):
            return Dat()

        # IDT
        elif match("<"):
            name = parse_name()
            skip = parse_exact(":")
            type = parse_term(context)
            ctrs = []
            while match("|"):
                ctr_name = parse_name()
                ctr_skip = parse_exact(":")
                ctr_type = parse_term(context.extend((name, None)))
                ctrs.append((ctr_name, ctr_type))
            parse_exact(">")
            return Idt(name, type, ctrs)

        # IDT Type
        elif match("!"):
            data = parse_term(context)
            return Ity(data)

        # IDT Constructor
        elif match("@"):
            data = parse_term(context)
            skip = parse_exact(".")
            name = parse_name()
            return Con(data, name)

        # IDT Induction
        elif match("?"):
            data = parse_term(context)
            vars = data.to_inductive().get_vars()
            term = parse_term(context)
            skip = parse_exact("->")
            moti = parse_term(reduce(lambda ctx, var: ctx.extend((var, None)), vars[0], context))
            cses = []
            for (ctr_name, ctr_vars) in vars[1]:
                skip = parse_exact("|")
                skip = parse_exact(ctr_name)
                skip = parse_exact("=>")
                body = parse_term(reduce(lambda ctx, var: ctx.extend((var, None)), ctr_vars, context))
                cses.append(body)
            skip = parse_exact(";")
            return Ind(data, term, moti, cses)

        # Variable (Bruijn indexed)
        elif match("#"):
            index = parse_name()
            return Var(int(index))

        # Variable (named)
        else:
            name = parse_name()
            skip = 0
            while match("'"):
                skip += 1
            bind = context.find_by_name(name, skip)
            if bind:
                return bind[1]
            raise(Exception("Unbound variable: '" + str(name) + "' at index " + str(Cursor.index) + "-"))

    return parse_term(Context())

test = """
    -- Unit
    def the [P : Type] [x : P]
        x

    -- Booleans
    def Bool
        < Bool  : Type
        | true  : Bool
        | false : Bool >

    -- Bool constructors
    def true @Bool.true
    def false @Bool.false

    -- Inducton on Bool
    def bool_induction
        [b : !Bool]
        [P : {b : !Bool} Type]
        [T : (P @Bool.true)]
        [F : (P @Bool.false)]
        ? Bool b -> (P self)
        | true   => T
        | false  => F ;

    -- Bool negation
    def not [b : !Bool]
        ? Bool b -> !Bool
        | true   => @Bool.false
        | false  => @Bool.true;

    -- Natural numbers
    def Nat
        < Nat  : Type
        | succ : {pred : Nat} Nat
        | zero : Nat >

    -- Nat examples
    def n0 @Nat.zero
    def n1 (@Nat.succ n0)
    def n2 (@Nat.succ n1)
    def n3 (@Nat.succ n2)
    def n4 (@Nat.succ n3)

    -- Nat induction
    def nat_induction
        [n : !Nat]
        [P : {n : !Nat} Type]
        [S : {-n : !Nat} {p : (P n)} (P (@Nat.succ n))]
        [Z : (P @Nat.zero)]
        ? Nat n -> (P self)
        | succ  => (S -pred_index pred)
        | zero  => Z ;

    -- Nat addition
    def add [a : !Nat]
        ? Nat a -> {b : !Nat} !Nat
        | succ  => [b : !Nat] (@Nat.succ (pred b))
        | zero  => [b : !Nat] b ;

    -- Nat multiplication
    def mul [n : !Nat] [m : !Nat]
        ? Nat n -> !Nat
        | succ  => (add m pred)
        | zero  => @Nat.zero ;

    def Zup
        < Zup : {a : !Bool} {b : !Bool} Type
        | zip : (Zup @Bool.false @Bool.true) 
        | zap : (Zup @Bool.true @Bool.false) >

    def zup_test
        ? Zup @Zup.zip -> (? Bool b -> Type | true => !Bool | false => !Nat ;)
        | zip => @Bool.true
        | zap => @Nat.zero ;

    -- Example type indexed on Nat (just Vectors without elements)
    def Ind
        < Ind  : {n : !Nat} Type
        | step : {-n : !Nat} {i : (Ind n)} (Ind (@Nat.succ n))
        | base : (Ind @Nat.zero) >

    -- Ind examples
    def i0 @Ind.base
    def i1 (@Ind.step -n0 i0)
    def i2 (@Ind.step -n1 i1)
    def i3 (@Ind.step -n2 i2)
    def i4 (@Ind.step -n3 i3)

    -- From Nat to Ind
    def nat_to_ind [n : !Nat]
        ? Nat n -> (!Ind self)
        | succ  => (@Ind.step -pred_index pred)
        | zero  => @Ind.base ;

    -- Equality
    def Eq
        < Eq   : {-A : Type} {a : A} {b : A} Type
        | refl : {-A : Type} {t : A} (Eq -A t t) >

    -- Symmetry of equality
    def sym [A : Type] [a : A] [b : A] [e : (!Eq -A a b)]
        ? Eq e -> (!Eq -A b a)
        | refl => (@Eq.refl -A t) ;

    -- Congruence of equality
    def cong [A : Type] [B : Type] [x : A] [y : A] [e : (!Eq -A x y)]
        ? Eq e -> {f : {x : A} B} (!Eq B (f a) (f b))
        | refl => [f : {x : A} B] (@Eq.refl -B (f t)) ;

    -- Substitution of equality
    def subst [A : Type] [x : A] [y : A] [e : (!Eq -A x y)]
        ? Eq e -> {P : {x : A} Type} {px : (P a)} (P b)
        | refl => [P : {x : A} Type] [px : (P t)] px ;

    -- n + 0 == n
    def add_n_zero [n : !Nat]
        ? Nat n -> (!Eq -!Nat (add self @Nat.zero) self)
        | succ  => (cong !Nat !Nat (add pred_index @Nat.zero) pred_index pred [x : !Nat] (@Nat.succ x))
        | zero  => (@Eq.refl -!Nat @Nat.zero);

    -- n + S(m) == S(n + m)
    def add_n_succ_m [n : !Nat]
        ? Nat n -> {m : !Nat} (!Eq -!Nat (add self (@Nat.succ m)) (@Nat.succ (add self m)))
        | succ => [m : !Nat]
            (cong !Nat !Nat
                (add pred_index (@Nat.succ m))
                (@Nat.succ (add pred_index m))
                (pred m)
                @Nat.succ)
        | zero  => [m : !Nat]
            (@Eq.refl -!Nat (@Nat.succ m));

    add_n_succ_m
"""

def test_all():
    term = string_to_term(test)

    print "Input term:"
    print term.to_string(Context())
    print ""

    print "Inferred type:"
    #print term.check(Context()).eval(False).to_string(Context())
    print term.check(Context()).eval(True).to_string(Context())
    print ""

    print "Normal form:"
    #print term.eval(False).to_string(Context())
    print term.eval(True).to_string(Context())
    print ""

test_all()
