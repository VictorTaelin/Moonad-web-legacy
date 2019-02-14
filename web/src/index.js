const formality = require("formality-lang");


var term = formality.parse("main = ([s] [z] (s (s z)) [s] [z] (s (s z)))").main.term;
var norm = formality.norm(term);

function component() {
  let element = document.createElement('div');

  // Lodash, currently included via a script, is required for this line to work
  element.innerHTML = formality.show(norm);

  return element;
}

document.body.appendChild(component());
