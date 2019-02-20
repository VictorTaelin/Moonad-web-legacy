// Converts a JavaScript string of 0s and 1s to a Formality Bin
function bitstring_to_term(bits) {
  var LamP = term => F.Lam(true, "P", null, term);
  var LamO = term => F.Lam(false, "O", null, term);
  var LamI = term => F.Lam(false, "I", null, term);
  var LamE = term => F.Lam(false, "E", null, term);
  var O    = term => LamP(LamO(LamI(LamE(F.App(false,F.Var(2),term)))));
  var I    = term => LamP(LamO(LamI(LamE(F.App(false,F.Var(1),term)))));
  var term = LamP(LamO(LamI(LamE(F.Var(0)))));
  for (var i = 0; i < bits.length; ++i) {
    term = (bits[i] === "0" ? O : I)(term);
  }
  return term;
}

// Converts a Formality Bin to a JavaScript string of 0s and 1s
function term_to_bitsring(term, bits = "") {
  var term = F.erase(term);
  var body = term[1].body[1].body[1].body;
  if (body[0] === "App") {
    var bit = body[1].func[1].index === 2 ? "0" : "1";
    return bitstring_to_term(body[1].argm, bit + bits);
  } else {
    return bits;
  }
}

module.exports = {bitstring_to_term, term_to_bitstring};
