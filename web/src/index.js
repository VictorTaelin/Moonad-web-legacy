const F = require("formality-lang");
const I = require("nano-ipfs-store").at("https://ipfs.infura.io:5001"); 

var term = F.parse("main = ([s] [z] (s (s z)) [s] [z] (s (s z)))").main.term;
var norm = F.norm(term);

var code =
`s    = [n] [z] [s] (s n)
z    = [z] [s] z
0    = z
1    = (s 0)
2    = (s 1)
3    = (s 2)
4    = (s 3)
mul2 = [n] (n zero [m] (s (s (mul2 m))))
show = [n] (n [s] [z] z [m] [s] [z] (s (show m s z)))

Unit
: Type
= {P : Type} {new : Unit} P

Unit.new
: Unit
= [P] [new] new
`;

window.onload = () => {
  var console_input = document.getElementById("console-input");
  var console_log = document.getElementById("console-log");
  var code_editor = document.getElementById("code-editor");

  var state = {
    code: code,
    input: "",
    log: []
  };

  function log(text, bold = false) {
    state.log.push({text, bold});
  }

  log("Welcome to Moonad!", true);
  log("Enter a command or `help` to get started.");
  log("");

  function render() {
    code_editor.value = state.code;
    console_input.innerText = "» " + state.input + "█";
    console_log.innerText = "";
    for (var i = 0; i < state.log.length; ++i) {
      var line = document.createElement("div");
      line.style.fontFamily = "inherit";
      line.style.fontSize = "inherit";
      line.innerText = state.log[i].text || ".";
      line.style.visibility = !state.log[i].text ? "hidden" : null;
      line.style.textDecoration = state.log[i].bold ? "underline" : null;
      console_log.appendChild(line);
    }
    console_log.scrollTop = console_log.scrollHeight;
  }

  function execute(command) {
    var split_index = command.indexOf(" ");
    var split_index = split_index === -1 ? command.length : split_index;
    var action = command.slice(0, split_index);
    var argument = command.slice(split_index + 1);
    try {
      var defs = F.parse(state.code);
    } catch (e) {
      log("Error parsing code: ...", true);
      log("");
      return;
    }
    try {
      switch (action) {
        case "eval":
        case "e":
          log("Evaluating `" + argument + "`:", true);
          log(F.show(F.norm(F.parse("main = " + argument).main.term, defs)));
          log("");
          break;
        case "check":
        case "c":
          log("Checking `" + argument + "`:", true);
          log(F.show(F.infer(F.parse("main = " + argument).main.term, defs)));
          log("");
          break;
        case "clear":
          state.log = [];
          break;
        case "help":
          log("Available commands:", true);
          log("");
          log("eval <term>");
          log("- evaluates a term to normal form");
          log("");
          log("check <term>");
          log("- checks the type of a term");
          log("");
          log("clear");
          log("- clears the console");
          log("");
          log("save");
          log("- saves the program on IPFS");
          log("");
          log("load");
          log("- loads a program from IPFS");
          log("");
          break;
        case "save":
          log("Saving code to IPFS...");
          I.add(state.code)
            .then((hash) => {
              log("Code saved. Hash: `" + hash + "`.");
              render();
            });
          break;
        case "load":
          log("Loading code from IPFS...");
          I.cat(argument).then((code) => {
            state.code = code;
            log("Done!");
            render();
          });
          break;
        default:
          log("Unknown command.", true);
          log("");
          break;
      }
    } catch (e) {
      var lines = e.split("\n");
      for (var i = 0; i < lines.length; ++i) {
        log(lines[i]);
      }
      return;
    }
  }

  document.onkeypress = (e) => {
    if (document.activeElement.id !== "code-editor" && !e.metaKey && !e.ctrlKey) {
      if (e.key === "Enter") {
        execute(state.input);
        state.input = "";
      } else if (e.key === "Backspace") {
        state.input = state.input.slice(0, -1);
      } else if (e.key.length === 1) {
        state.input += e.key;
      }
      render();
    }
  };

  document.onpaste = (e) => {
    if (document.activeElement.id !== "code-editor") {
      state.input += e.clipboardData.getData('text/plain');
      render();
    }
  };

  document.onkeyup = (e) => {
    if (document.activeElement.id === "code-editor") {
      state.code = code_editor.value;
      render();
    }
  }

  render();
};
