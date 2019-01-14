# This file is outdated. We're using dependent intersections instead. See javascript/formaltiy.js

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

    def find_by_name(self, find_name, skip, only_data):
        for (name, term) in self.list:
            if find_name == name:
                if only_data and not isinstance(term.eval(False), Idt):
                    pass
                elif skip > 0:
                    skip = skip - 1
                else:
                    return (name, term)
        return None

    def show(self):
        if len(self.list) == 0:
            return "(empty)\n"
        else:
            text = ""
            for (name, value) in reversed(self.list):
                text += "-- " + name + " : " + value.to_string(self) + "\n"
            return text

    def show_mismatch(self, expect, actual, value):
        text  = "Type mismatch on " + value + ".\n"
        text += "- Expect: " + expect.to_string(self) + "\n"
        text += "- Actual: " + actual.to_string(self) + "\n"
        text += "- Context:\n" + self.show()
        return text

class Nik:
    def __init__(self, name, term):
        self.name = name
        self.term = term

    def to_string(self, context):
        return self.name

    def shift(self, depth, inc):
        return Nik(self.name, self.term.shift(depth, inc))

    def subst(self, depth, val):
        return Nik(self.name, self.term.subst(depth, val))

    def uses(self, depth):
        return self.term.uses(depth)

    def equal(self, other):
        return self.term.equal(other)

    def eval(self, erase):
        return self.term.eval(erase)

    def check(self, context):
        return self.term.check(context)
        
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

    def eval(self, erase):
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
        eras = ("-" if self.eras else "")
        name = self.name
        bind = " : " + self.bind.to_string(context)
        body = self.body.to_string(context.extend((self.name, self.bind)))
        return "{" + eras + name + bind + "} " + body

    def shift(self, depth, inc):
        eras = self.eras
        name = self.name 
        bind = self.bind.shift(depth, inc)
        body = self.body.shift(depth + 1, inc)
        return All(eras, name, bind, body)

    def subst(self, depth, val):
        eras = self.eras
        name = self.name
        bind = self.bind.subst(depth, val)
        body = self.body.subst(depth + 1, val and val.shift(0, 1))
        return All(eras, name, bind, body)

    def uses(self, depth):
        bind = self.bind.uses(depth)
        body = self.body.uses(depth + 1)
        return bind + body

    def equal(self, other):
        if isinstance(other, All):
            eras = self.eras == other.eras
            bind = self.bind.equal(other.bind)
            body = self.body.equal(other.body)
            return eras and bind and body
        return False

    def eval(self, erase):
        eras = self.eras
        name = self.name
        bind = self.bind.eval(erase)
        body = self.body.eval(erase)
        return All(eras, name, bind, body)

    def check(self, context):
        bind_v = self.bind
        bind_t = self.bind.check(context)
        body_t = self.body.check(context.extend((self.name, bind_v)))
        if not bind_t.eval(True).equal(Typ()) or not body_t.eval(True).equal(Typ()):
            raise(Exception("Forall not a type. Context:\n" + context.show()))
        return Typ()

class Lam:
    def __init__(self, eras, name, bind, body):
        self.eras = eras
        self.name = name
        self.bind = bind
        self.body = body

    def to_string(self, context):
        eras = "-" if self.eras else ""
        name = self.name
        bind = " : " + self.bind.to_string(context) if self.bind else ""
        body = self.body.to_string(context.extend((self.name, None)))
        return "[" + eras + name + bind + "] " + body

    def shift(self, depth, inc):
        eras = self.eras
        name = self.name
        bind = self.bind and self.bind.shift(depth, inc)
        body = self.body.shift(depth + 1, inc)
        return Lam(eras, name, bind, body)

    def subst(self, depth, val):
        eras = self.eras
        name = self.name
        bind = self.bind and self.bind.subst(depth, val)
        body = self.body.subst(depth + 1, val and val.shift(0, 1))
        return Lam(eras, name, bind, body)

    def uses(self, depth):
        uses = self.bind.uses(depth)
        body = self.body.uses(depth + 1)
        return uses + body

    def equal(self, other):
        if isinstance(other, Lam):
            eras = self.eras == other.eras
            body = self.body.equal(other.body)
            return eras and body
        return False

    def eval(self, erase):
        if erase and self.eras:
            return self.body.eval(erase).subst(0, None)
        else:
            eras = self.eras
            name = self.name
            bind = None if erase else self.bind.eval(erase)
            body = self.body.eval(erase)
            return Lam(eras, name, bind, body)

    def check(self, context):
        if self.bind is None:
            raise(Exception("Can't infer non-annotated lambda. Context:", context.show()))
        else:
            bind_v = self.bind
            bind_t = self.bind.check(context)
            body_t = self.body.check(context.extend((self.name, bind_v)))
            if not bind_t.eval(True).equal(Typ()):
                raise(Exception("Function type not a type. Context:", context.show()))
            return All(self.eras, self.name, bind_v, body_t)

class App:
    def __init__(self, eras, func, argm):
        self.eras = eras
        self.func = func
        self.argm = argm

    def to_string(self, context):
        text = ")"
        while isinstance(self, App):
            text = " " + ("-" if self.eras else "") + self.argm.to_string(context) + text
            self = self.func
        text = "(" + self.to_string(context) + text
        return text

    def shift(self, depth, inc):
        eras = self.eras
        func = self.func.shift(depth, inc)
        argm = self.argm.shift(depth, inc)
        return App(eras, func, argm)

    def subst(self, depth, val):
        eras = self.eras
        func = self.func.subst(depth, val)
        argm = self.argm.subst(depth, val)
        return App(eras, func, argm)

    def uses(self, depth):
        return self.func.uses(depth) + self.argm.uses(depth)

    def equal(self, other):
        if isinstance(other, App):
            eras = self.eras == other.eras
            func = self.func.equal(other.func)
            argm = self.argm.equal(other.argm)
            return eras and func and argm
        return False

    def eval(self, erase):
        if erase and self.eras:
            return self.func.eval(erase)
        else:
            func_v = self.func.eval(erase)
            if not isinstance(func_v, Lam):
                return App(self.eras, func_v, self.argm.eval(erase))
            return func_v.body.subst(0, self.argm).eval(erase)

    def check(self, context):
        func_t = self.func.check(context)
        argm_t = self.argm.check(context)
        func_T = func_t.eval(True)
        expect = func_T.bind
        actual = argm_t.eval(True)
        if not isinstance(func_T, All):
            raise(Exception("Non-function application. Context:\n" + context.show()))
        if func_T.eras != self.eras:
            raise(Exception("Mismatched erasure on " + self.to_string(context) + "."))
        if not expect.equal(actual):
            raise(Exception(context.show_mismatch(expect, actual, self.to_string(context) + " application")))
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
                return App(False,Typ(),Typ())
                raise(Exception("Use of erased variable."))
            else:
                return val
        return Var(self.index - (1 if self.index > depth else 0))
        
    def uses(self, depth):
        return 1 if depth == self.index else 0

    def equal(self, other):
        return isinstance(other, Var) and self.index == other.index

    def eval(self, erase):
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

    def eval(self, erase):
        return Dat()

    def check(self, context):
        return Typ()

class Idt:
    def __init__(self, name, moti, ctrs):
        self.name = name # string
        self.moti = moti # term
        self.ctrs = ctrs # [(string, term)]

    def to_string(self, context):
        text = "($ " + self.name + " : " + self.moti.to_string(context)
        for (i, (ctr_name, ctr_moti)) in enumerate(self.ctrs):
            text += " | " + ctr_name + " : " + ctr_moti.to_string(context.extend((self.name, self.moti)))
        return text + " ;)"

    def shift(self, depth, inc):
        name = self.name
        moti = self.moti.shift(depth, inc)
        ctrs = [(ctr_name, ctr_type.shift(depth + 1, inc)) for (ctr_name, ctr_type) in self.ctrs]
        return Idt(name, moti, ctrs)

    def subst(self, depth, val):
        name = self.name
        moti = self.moti.subst(depth, val)
        ctrs = [(ctr_name, ctr_type.subst(depth + 1, val.shift(0, 1))) for (ctr_name, ctr_type) in self.ctrs]
        return Idt(name, moti, ctrs)

    def uses(self, depth):
        moti = self.moti.uses(depth)
        ctrs = sum([ctr_type.uses(depth + 1) for (_, ctr_type) in self.ctrs])
        return moti + ctrs

    def equal(self, other):
        if isinstance(other, Idt):
            moti = self.moti.equal(other.moti)
            ctrs = all([a[1].equal(b[1]) for (a,b) in zip(self.ctrs, other.ctrs)])
            return moti and ctrs
        return False

    def eval(self, erase):
        name = self.name
        moti = self.moti.eval(erase)
        ctrs = [(ctr_name, ctr_type.eval(erase)) for (ctr_name, ctr_type) in self.ctrs]
        return Idt(name, moti, ctrs)

    def check(self, context):
        return Dat()

    def get_vars(self):
        moti_vars = []
        self_moti = self.moti
        while isinstance(self_moti, All):
            moti_vars.append(self_moti.name)
            self_moti = self_moti.body
        ctrs_vars = []
        for (ctr_name, ctr_type) in self.ctrs:
            ctr_vars = []
            while isinstance(ctr_type, All):
                ctr_vars.append(ctr_type.name)
                ctr_type = ctr_type.body
            ctrs_vars.append((ctr_name, ctr_vars))
        return (moti_vars, ctrs_vars)

    def derive_type(self):
        def build_indices(depth, indices_type):
            if isinstance(indices_type, All):
                eras = indices_type.eras
                name = indices_type.name
                bind = indices_type.bind
                body = build_indices(depth + 1, indices_type.body)
                return Lam(eras, name, bind, body)
            else:
                return build_motive(depth)

        def build_motive(depth):
            eras = True
            name = self.name
            bind = self.moti.shift(0, depth)
            body = build_constructor(depth + 1, 0)
            return All(eras, name, bind, body)

        def build_constructor(depth, num):
            if num < len(self.ctrs):
                (ctr_name, ctr_type) = self.ctrs[num]
                eras = False
                name = ctr_name
                bind = ctr_type.shift(1, depth).subst(0, Var(num))
                body = build_constructor(depth + 1, num + 1)
                return All(eras, name, bind, body)
            else:
                return build_return_type(depth, self.moti, 0, Var(len(self.ctrs)))

        def build_return_type(depth, indices_type, index, return_type):
            if isinstance(indices_type, All):
                return_type = App(indices_type.eras, return_type, Var(depth - index - 1))
                return build_return_type(depth, indices_type.body, index + 1, return_type)
            else:
                return return_type

        return build_indices(0, self.moti)

    def derive_constructor(self, name):
        for (ctr_index, (ctr_name, ctr_type)) in enumerate(self.ctrs):
            if name == ctr_name:
                break

        def build_lambdas(depth, fields_type):
            if isinstance(fields_type, All):
                eras = fields_type.eras
                name = fields_type.name
                bind = fields_type.bind
                body = build_lambdas(depth + 1, fields_type.body)
                return Lam(eras, name, bind, body)
            else:
                return build_body(depth, ctr_type, 0, Var(len(self.ctrs) - ctr_index - 1))

        def build_body(depth, fields_type, field_index, term):
            if isinstance(fields_type, All):
                field = Var(depth - field_index - 1)
                # TODO: currently only works for very simple recursive ocurrences
                if fields_type.bind.uses(field_index) > 0:
                    field = App(True, field, Var(len(self.ctrs)))
                    for i in xrange(len(self.ctrs)):
                        field = App(False, field, Var(len(self.ctrs) - i - 1))
                body = App(fields_type.eras, term, field)
                return build_body(depth, fields_type.body, field_index + 1, body)
            else:
                return term

        return build_lambdas(0, ctr_type.subst(0, self.derive_type()).eval(False))

    def to_inductive(self):
        def build_motive(depth, motive_type, self_type):
            if isinstance(motive_type, All):
                eras = motive_type.eras
                name = motive_type.name
                bind = motive_type.bind
                body = build_motive(depth + 1, motive_type.body, App(motive_type.eras, self_type.shift(0, 1), Var(0)))
                return All(eras, name, bind, body)
            else:
                return All(False, "self", self_type, motive_type)

        def build_constructor(depth, fields_type, self_value):
            if isinstance(fields_type, All):
                # TODO: currently only works for very simple recursive ocurrences
                if fields_type.bind.uses(depth) > 0:
                    eras_0 = True
                    name_0 = fields_type.name
                    bind_0 = fields_type.bind.subst(depth, self.derive_type().shift(0, depth))
                    eras_1 = fields_type.eras
                    name_1 = "~" + fields_type.name
                    bind_1 = App(False, fields_type.bind.shift(0, 1), Var(0))
                    newfty = fields_type.body.shift(0, 1)
                    newval = App(fields_type.eras, self_value.shift(0, 2), Var(1))
                    body_1 = build_constructor(depth + 2, newfty, newval)
                    return All(eras_0, name_0, bind_0, All(eras_1, name_1, bind_1, body_1))
                else:
                    eras_0 = fields_type.eras
                    name_0 = fields_type.name
                    bind_0 = fields_type.bind
                    newfty = fields_type.body
                    newval = App(fields_type.eras, self_value.shift(0, 1), Var(0))
                    body_0 = build_constructor(depth + 1, newfty, newval)
                    return All(eras_0, name_0, bind_0, body_0)
            else:
                return App(False, fields_type, self_value)

        ind_name = self.name + "_ind"
        ind_moti = build_motive(0, self.moti, self.derive_type())
        ind_ctrs = []
        for (ctr_name, ctr_type) in self.ctrs:
            ind_ctr_name = ctr_name
            ind_ctr_type = build_constructor(0, ctr_type, self.derive_constructor(ctr_name))
            ind_ctrs.append((ind_ctr_name, ind_ctr_type))
        return Idt(ind_name, ind_moti, ind_ctrs).eval(False)

class Ity:
    def __init__(self, data):
        self.data = data

    def to_string(self, context):
        return "&" + self.data.to_string(context)

    def shift(self, depth, inc):
        return Ity(self.data.shift(depth, inc))

    def subst(self, depth, val):
        return Ity(self.data.subst(depth, val))

    def uses(self, depth):
        return self.data.uses(depth)

    def equal(self, other):
        return isinstance(other, Ity) and self.data.equal(other.data)

    def eval(self, erase):
        data_v = self.data.eval(False)
        if isinstance(data_v, Idt):
            return data_v.derive_type().eval(erase)
        else:
            return Ity(data_v)

    def check(self, context):
        data_v = self.data.eval(False)
        if isinstance(data_v, Idt):
            return data_v.derive_type().check(context).eval(False)
        else:
            raise(Exception("Couldn't determine datatype statically. Context:\n" + context.show()))

class Con:
    def __init__(self, data, name):
        self.data = data
        self.name = name

    def to_string(self, context):
        return "@" + self.data.to_string(context) + "." + self.name

    def shift(self, depth, inc):
        data = self.data.shift(depth, inc)
        name = self.name
        return Con(data, name)

    def subst(self, depth, val):
        data = self.data.subst(depth, val)
        name = self.name
        return Con(data, name)

    def uses(self, depth):
        return self.data.uses(depth)

    def equal(self, other):
        if isinstance(other, Con):
            data = self.data.equal(other.data)
            name = self.name == other.name
            return data and name
        return False

    def eval(self, erase):
        data_v = self.data.eval(False)
        if isinstance(data_v, Idt):
            return data_v.derive_constructor(self.name).eval(erase)
        else:
            return Con(data_v, self.name)

    def check(self, context):
        data_v = self.data.eval(False)
        if isinstance(data_v, Idt):
            return data_v.derive_constructor(self.name).check(context).eval(False)
        else:
            raise(Exception("Couldn't determine datatype statically. Context:\n" + context.show()))

class Ind:
    def __init__(self, data, term, moti, cses):
        self.data = data
        self.term = term
        self.moti = moti
        self.cses = cses

    def to_string(self, context):
        vars = self.data.eval(False).to_inductive().get_vars()
        text = "(?" + self.data.to_string(context)
        text += " " + self.term.to_string(context) + " ->"
        text += " " + self.moti.to_string(reduce(lambda ctx, var: ctx.extend((var, None)), vars[0], context))
        for (i, (ctr_name, ctr_vars)) in enumerate(vars[1]):
            text += " | " + ctr_name + " => " + self.cses[i].to_string(reduce(lambda ctx, var: ctx.extend((var, None)), ctr_vars, context))
        return text + " ;)"

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
        indu = self.data.eval(False).to_inductive()
        vars = indu.get_vars()
        moti = build_term(indu.moti, self.moti, len(vars[0]))
        cses = []
        for (ctr_index, ((ctr_name, ctr_type), ctr_body)) in enumerate(zip(indu.ctrs, self.cses)):
            ctr_type = ctr_type.subst(0, moti).eval(False)
            ctr_term = build_term(ctr_type, ctr_body, len(vars[1][ctr_index][1]))
            cses.append((ctr_name, ctr_term, ctr_type))
        return (moti, cses)

    def shift(self, depth, inc):
        vars = self.data.eval(False).to_inductive().get_vars()
        data = self.data.shift(depth, inc)
        term = self.term.shift(depth, inc)
        moti = self.moti.shift(depth + len(vars[0]), inc)
        ctrs = [self.cses[i].shift(depth + len(vars[1][i]), inc) for i in xrange(len(self.cses))]
        return Ind(data, term, moti, ctrs)

    def subst(self, depth, val):
        vars = self.data.eval(False).to_inductive().get_vars()
        data = self.data.subst(depth, val)
        term = self.term.subst(depth, val)
        moti = self.moti.subst(depth + len(vars[0]), val)
        ctrs = [self.cses[i].subst(depth + len(vars[1][i]), val) for i in xrange(len(self.cses))]
        return Ind(data, term, moti, ctrs)

    def uses(self, depth):
        vars = self.data.eval(False).to_inductive().get_vars()
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

    def eval(self, erase):
        if not erase:
            data = self.data.eval(erase)
            term = self.term.eval(erase)
            moti = self.moti.eval(erase)
            ctrs = [self.cses[i].eval(erase) for i in xrange(len(self.cses))]
            return Ind(data, term, moti, ctrs)
        else:
            (moti, cses) = self.build()
            term = App(True, self.term, moti)
            for (cse_name, cse_term, cse_type) in cses:
                term = App(False, term, cse_term)
            return term.eval(erase)

    def check(self, context):
        # Check term type
        indices = self.get_indices(context)
        term_t = self.term.check(context)
        data_t = self.data.eval(False).derive_type()
        for idx in indices:
            data_t = data_t.body.subst(0, idx)
        expect = term_t.eval(True)
        actual = data_t.eval(True)
        if not expect.equal(actual):
            raise(Exception(context.show_mismatch(expect, actual, "term of " + self.to_string(context))))

        # Check case types
        (moti, cses) = self.build()
        for (cse_name, cse_term, cse_type) in cses:
            expect = cse_type.eval(True)
            actual = cse_term.check(context).eval(True)
            if not expect.equal(actual):
                raise(Exception(context.show_mismatch(expect, actual, "case " + cse_name + " of " + self.to_string(context))))

        # Build return type
        result = moti.eval(False)
        for idx in indices:
            result = result.body.subst(0, idx)
        result = result.body.subst(0, self.term)
        return result

def string_to_term(code):
    class Cursor:
        index = 0

    def is_space(char):
        return char in " \t\n"

    def is_name_char(char):
        return char in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_~"

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

    def error(text):
        text += "This is the relevant code:\n\n<<<"
        text += code[Cursor.index - 64 : Cursor.index] + "<<<HERE>>>"
        text += code[Cursor.index : Cursor.index + 64] + ">>>"
        raise(Exception(text))

    def parse_exact(string):
        if not match(string):
            error("Parse error, expected '" + string + "'.\n")
        
    def parse_name():
        skip_spaces()
        name = ""
        while Cursor.index < len(code) and is_name_char(code[Cursor.index]):
            name = name + code[Cursor.index]
            Cursor.index += 1
        return name
        
    def parse_term(context, only_data):
        # Comment
        if match("--"):
            while Cursor.index < len(code) and code[Cursor.index] != "\n":
                Cursor.index += 1
            return parse_term(context, False)

        # Application
        elif match("("):
            func = parse_term(context, False)
            while Cursor.index < len(code) and not match(")"):
                eras = match("-")
                argm = parse_term(context, False)
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
            bind = parse_term(context, False)
            skip = parse_exact("}")
            body = parse_term(context.extend((name, None)), False)
            return All(eras, name, bind, body)

        # Lambda
        elif match("["):
            eras = match("-")
            name = parse_name()
            skip = parse_exact(":")
            bind = parse_term(context, False)
            skip = parse_exact("]")
            body = parse_term(context.extend((name, None)), False)
            return Lam(eras, name, bind, body)

        # Definition
        elif match("def"):
            name = parse_name()
            term = parse_term(context, False)
            body = parse_term(context.extend((name, term)), False)
            return body

        # Data
        elif match("Data"):
            return Dat()

        # IDT (inline)
        elif match("$") or match("data"):
            inli = code[Cursor.index - 1] == "$"
            name = parse_name()
            skip = parse_exact(":")
            type = parse_term(context, False)
            ctrs = []
            while match("|"):
                ctr_name = parse_name()
                ctr_skip = parse_exact(":")
                ctr_type = parse_term(context.extend((name, None)), False)
                ctrs.append((ctr_name, ctr_type))
            parse_exact(";")
            data = Idt(name, type, ctrs)
            # Inline declaration
            if inli:
                return data
            # Global declaration (creates defs)
            else:
                context = context.extend((name.upper(), data))
                context = context.extend((name, data))
                context = context.extend((name, Ity(data)))
                for ctr in ctrs:
                    context = context.extend((ctr[0], Con(data, ctr[0])))
                return parse_term(context, False)

        # IDT Type
        elif match("&"):
            data = parse_term(context, True)
            return Ity(data)

        # IDT Constructor
        elif match("@"):
            data = parse_term(context, True)
            skip = parse_exact(".")
            name = parse_name()
            return Con(data, name)

        # IDT Induction
        elif match("?"):
            data = parse_term(context, True)
            vars = data.eval(False).to_inductive().get_vars()
            term = parse_term(context, False)
            skip = parse_exact("->")
            moti = parse_term(reduce(lambda ctx, var: ctx.extend((var, None)), vars[0], context), False)
            cses = []
            for (ctr_name, ctr_vars) in vars[1]:
                skip = parse_exact("|")
                skip = parse_exact(ctr_name)
                skip = parse_exact("=>")
                body = parse_term(reduce(lambda ctx, var: ctx.extend((var, None)), ctr_vars, context), False)
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
            bind = context.find_by_name(name, skip, only_data)
            if bind:
                return Nik(name, bind[1])
            error("Parse error, unbound variable '" + name + "'.\n")

    return parse_term(Context(), False)

test = """
    -- Unit
    def the [P : Type] [x : P]
        x

    -- Booleans
    data Bool : Type
    | true    : Bool
    | false   : Bool;

    -- Inducton on Bool
    def bool_induction
        [b : Bool]
        [P : {b : Bool} Type]
        [T : (P true)]
        [F : (P false)]
        ? Bool b -> (P self)
        | true   => T
        | false  => F ;

    -- Bool negation
    def not [b : Bool]
        ? Bool b -> Bool
        | true   => false
        | false  => true;

    -- Natural numbers
    data Nat : Type
    | succ   : {pred : Nat} Nat
    | zero   : Nat;

    -- Nat examples
    def n0 zero
    def n1 (succ n0)
    def n2 (succ n1)
    def n3 (succ n2)
    def n4 (succ n3)

    -- Nat induction
    def nat_induction
        [n  : Nat]
        [-P : {-n : Nat} Type]
        [S  : {-n : Nat} {p : (P -n)} (P -(succ n))]
        [Z  : (P -zero)]
        ? Nat n -> (P -self)
        | succ  => (S -pred ~pred)
        | zero  => Z ;

    -- Nat addition
    def add [a : Nat]
        ? Nat a -> {b : Nat} Nat
        | succ  => [b : Nat] (succ (~pred b))
        | zero  => [b : Nat] b ;

    -- Nat multiplication
    def mul [n : Nat] [m : Nat]
        ? Nat n -> Nat
        | succ  => (add m ~pred)
        | zero  => zero ;

    data Zup : {a : Bool} {b : Bool} Type
    | zip    : (Zup false true) 
    | zap    : (Zup true false) ;

    def zup_test
        ? Zup zip -> (? Bool b -> Type | true => Bool | false => Nat ;)
        | zip     => true
        | zap     => zero ;

    -- Example type indexed on Nat (just Vectors without elements)
    data Ind : {n : Nat} Type
    | step   : {-n : Nat} {i : (Ind n)} (Ind (succ n))
    | base   : (Ind zero) ;

    -- Ind examples
    def i0 base
    def i1 (step -n0 i0)
    def i2 (step -n1 i1)
    def i3 (step -n2 i2)
    def i4 (step -n3 i3)

    -- From Nat to Ind
    def nat_to_ind [n : Nat]
        ? Nat n -> (Ind self)
        | succ  => (step -pred ~pred)
        | zero  => base ;

    -- Equality
    data Eq : {-A : Type} {a : A} {b : A} Type
    | refl  : {-A : Type} {-t : A} (Eq -A t t) ;

    -- Symmetry of equality
    def sym [-A : Type] [-a : A] [-b : A] [e : (Eq -A a b)]
        ? Eq e -> (Eq -A b a)
        | refl => (refl -A -t) ;

    -- Congruence of equality
    def cong [-A : Type] [-B : Type] [-x : A] [-y : A] [e : (Eq -A x y)]
        ? Eq e -> {-f : {x : A} B} (Eq -B (f a) (f b))
        | refl => [-f : {x : A} B] (refl -B -(f t)) ;

    -- Substitution of equality
    def subst [-A : Type] [-x : A] [-y : A] [e : (Eq -A x y)]
        ? Eq e -> {-P : {x : A} Type} {px : (P a)} (P b)
        | refl => [-P : {x : A} Type] [px : (P t)] px ;

    -- n + 0 == n
    def add_n_zero [n : Nat]
        ? Nat n -> (Eq -Nat (add self zero) self)
        | succ  => (cong -Nat -Nat -(add pred zero) -pred ~pred -succ)
        | zero  => (refl -Nat -zero);

    -- n + S(m) == S(n + m)
    def add_n_succ_m [n : Nat]
        ? Nat n -> {m : Nat} (Eq -Nat (add self (succ m)) (succ (add self m)))
        | succ  => [m : Nat] (cong -Nat -Nat -(add pred (succ m)) -(succ (add pred m)) (~pred m) -succ)
        | zero  => [m : Nat] (refl -Nat -(succ m));

    add_n_succ_m

    def add_comm [n : Nat]
        ? Nat n -> {m : Nat} (Eq -Nat (add self m) (add m self))
        | succ  => [m : Nat]
            (subst -Nat -(add m pred) -(add pred m)
                (sym -Nat -(add pred m) -(add m pred) (~pred m))
                -[x : Nat](Eq -Nat (succ x) (add m (succ pred)))
                (sym -Nat -(add m (succ pred)) -(succ (add m pred)) (add_n_succ_m m pred)))
        | zero  => [m : Nat] (sym -Nat -(add m zero) -m (add_n_zero m));

    add_comm
"""

def test_all():
    try:
        term = string_to_term(test)
    except Exception as err:
        print err
        return

    print "Input term:"
    print term.to_string(Context())
    print ""

    try:
        print "Inferred type:"
        print term.check(Context()).eval(True).to_string(Context())
        print ""
    except Exception as err:
        print err
        print ""

    print "Normal form:"
    print term.eval(True).to_string(Context())
    print ""

test_all()
