import prelude from './prelude.formality';

const F = require("formality-lang");
const I = require("nano-ipfs-store").at("https://ipfs.infura.io:5001"); 

// Converts a JavaScript string of 0s and 1s to a Formality Bin
function write_bits(bits) {
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
function read_bits(term, bits = "") {
  var term = F.erase(term);
  var body = term[1].body[1].body[1].body;
  if (body[0] === "App") {
    var bit = body[1].func[1].index === 2 ? "0" : "1";
    return read_bits(body[1].argm, bit + bits);
  } else {
    return bits;
  }
}

window.onload = () => {
  var console_input = document.getElementById("console-input");
  var console_log = document.getElementById("console-log");
  var code_editor = document.getElementById("code-editor");

  var state = {
    code: prelude,
    input: "",
    log: [],
    apps: []
  };

  function log(value, bold = false) {
    state.log.push({value, bold});
  }

  log("Welcome to Moonad!", true);
  log("Enter a command or `help` to get started.");
  log("");

  function render() {
    code_editor.value = state.code;
    console_input.innerText = "» " + state.input + "█";
    console_log.innerText = "";
    for (var i = 0; i < state.log.length; ++i) {
      if (typeof state.log[i].value === "string") {
        var line = document.createElement("div");
        line.style.fontFamily = "inherit";
        line.style.fontSize = "inherit";
        line.innerText = state.log[i].value || ".";
        line.style.visibility = !state.log[i].value ? "hidden" : null;
        line.style.textDecoration = state.log[i].bold ? "underline" : null;
        console_log.appendChild(line);
      } else {
        console_log.appendChild(state.log[i].value);
      }
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
      console.log(e);
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
          state.apps = [];
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
          log("save");
          log("- saves the program on IPFS");
          log("");
          log("load <hash>");
          log("- loads a program from IPFS");
          log("");
          log("clear");
          log("- clears the console");
          log("");
          log("play <term>");
          log("- runs a Formality App");
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
        case "play":
          var term = F.Ref(argument || "main");
          log("Playing `" + term[1].name + "`.");
          try {
            F.check(term, F.App(false, F.Ref("App"), term), defs);
          } catch (e) {
            log("Error: `"+term[1].name+"` isn't a App.");
          }
          var init = F.App(false, F.Ref("App.init"), term);
          var next = F.App(false, F.Ref("App.next"), term);
          var draw = F.App(false, F.Ref("App.draw"), term);
          var st = F.norm(init, defs);

          var app = document.createElement("canvas");
          app.width = 256;
          app.height = 256;
          app.style.width = "128px";
          app.style.height = "128px";
          app.getContext("2d").scale(2,2);
          app.state = F.norm(init, defs);
          app.style.border = "1px solid black";
          app.style.marginTop = "6px";
          app.style.marginBottom = "6px";
          app.selected = true;
          app.render = () => {
            var ctx = app.getContext("2d");
            var bits = read_bits(F.norm(F.App(false, draw, app.state), defs));
            ctx.textAlign = "center";
            ctx.textBaseline = "middle";
            ctx.clearRect(0, 0, app.width, app.height);
            ctx.font = "12px Courier New";
            ctx.fillText(parseInt(bits || "0", 2), 64, 64);
            app.style.border = app.selected ? "2px solid #8888FF" : "1px solid black";
          }
          app.onclick = () => {
            app.selected = !app.selected;
            app.render();
          }
          app.key = (key) => {
            app.state = F.norm(F.App(false, F.App(false, next, F.Typ()), app.state), defs);
            app.render();
          }
          app.render();
          state.apps.push(app);
          log(app);

          break;
        default:
          log("Unknown command.", true);
          log("");
          break;
      }
    } catch (e) {
      console.log(e);
      var lines = e.split("\n");
      for (var i = 0; i < lines.length; ++i) {
        log(lines[i]);
      }
      return;
    }
  }

  document.onkeydown = (e) => {
    if (document.activeElement.id !== "code-editor" && !e.metaKey && !e.ctrlKey) {
      var interacted = false;
      for (var i = 0; i < state.apps.length; ++i) {
        if (state.apps[i].selected) {
          state.apps[i].key(e.key);
          interacted = true;
        }
      }
      if (!interacted) {
        if (e.key === "Enter") {
          execute(state.input);
          state.input = "";
        } else if (e.key === "Backspace") {
          state.input = state.input.slice(0, -1);
        } else if (e.key.length === 1) {
          state.input += e.key;
        }
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
