const MSTORE = require("./moonad-store-api");
const IPFS = require("nano-ipfs-store").at("https://ipfs.infura.io:5001"); 
const FS = require("formality-sugars");
const FI = require("formality-io");
const FL = require("formality-lang");
const FP = require("formality-stdlib") + `
  greeter
  = (IO.ask "GET_LINE" "What is your name?" [name : (Str name)] 
    (IO.ask "PUT_LINE" (Str.concat "Hello, " name) [_ : (Str _)]
    IO.end))`;

function install(main) {
  var state = {
    inpt: "",
    defs: FL.parse(FS.desugar(FP)),
    logs: []
  };

  function log(value, bold = false) {
    state.logs.push({value, bold});
  }

  function render() {
    function Box() {
      var element = document.createElement("div");
      element.style.margin = "0px";
      element.style.padding = "0px";
      element.style.boxSizing = "border-box";
      element.style.whiteSpace = "nowrap";
      return element;
    }
    function Line(text) {
      var element = document.createElement("pre");
      element.style.margin = "0px";
      element.style.padding = "0px";
      element.style.boxSizing = "border-box";
      element.style.height = "16px";
      element.textContent = text;
      return element;
    }
    main.innerHTML = "";
    main.style.width = "100%";
    main.style.height = "100%";
    main.style.fontFamily = "'Courier New', monospace";
    main.style.fontSize = 14 + "px";
    main.style.overflowX = "hidden";
    main.style.overflowY = "auto";
    main.appendChild(Line("> " + state.inpt));
    main.appendChild(Line(""));
    for (var i = 0; i < state.logs.length; ++i) {
      if (typeof state.logs[i].value === "string") {
        var line = Line(state.logs[i].value || ".");
        line.style.fontFamily = "inherit";
        line.style.fontSize = "inherit";
        line.style.visibility = !state.logs[i].value ? "hidden" : null;
        line.style.textDecoration = state.logs[i].bold ? "underline" : null;
        main.appendChild(line);
      } else {
        main.appendChild(state.logs[i].value);
      }
    }
  }

  function get_expr(expr) {
    return FL.parse("tmp_expr = " + "(" + (expr || "main") + ")").tmp_expr.term;
  }

  function log_error(e) {
    console.log(e);
    (typeof e === "string" ? e : e.toString()).split("\n").forEach(log);
    log("");
  }

  function execute(command) {
    var split_index = command.indexOf(" ");
    var split_index = split_index === -1 ? command.length : split_index;
    var action = command.slice(0, split_index);
    var argument = command.slice(split_index + 1);
    state.logs = [];
    switch (action) {
      case "help":
        log("Available commands:", true);
        log("list <str>  : lists available terms matching <str>");
        log("view <name> : views a term");
        log("type <expr> : type-checks an expression");
        log("eval <expr> : evaluates an expression");
        log("exec <name> : executes an IO term (try: `exec greeter`)");
        log("2evm <name> : compiles a Formality contract to EVM (TODO)");
        log("ipfs-load   : loads code from IPFS");
        log("ipfs-save   : saves a term to IPFS");
        log("eth-rpc     : (TODO)");
        log("eth-sign    : (TODO)");
        log("eth-deploy  : (TODO)");
        log("keccak256   : (TODO)");
        log("");
        break;
      case "list":
        log("Listing terms that match `" + argument + "`:", true);
        var str = argument || "";
        for (var name in state.defs) {
          if (name.indexOf(str) !== -1) {
            log("- " + name);
          }
        }
        log("");
        break;
      case "view":
        log(argument, true);
        if (state.defs[argument]) {
          var def = state.defs[argument];
          console.log(def);
          def.code.split("\n").slice(1,-1).forEach(line => log(line));
          log("");
        } else {
          log("Not found.");
        }
        log("");
        break;
      case "type":
        try {
          log("Type-checking `" + argument + "`:", true);
          log(FL.show(FL.infer(get_expr(argument), state.defs)));
          log("");
        } catch (e) {
          log_error(e);
        }
        break;
      case "exec":
      case "play":
        try {
          var expr = get_expr(argument);
          log("Executing `" + argument + "`.", true);
          try {
            FL.check(expr, FL.App(FL.Ref("IO"), expr), state.defs);
          } catch (e) {
            log("Not an IO type.");
            log("");
            return;
          }
          FI.run_IO_with(expr, state.defs, {
            GET_LINE: (arg) => new Promise((res) => {
              setTimeout(() => {
                var answer = window.prompt(arg);
                res(answer);
                render();
              }, 0);
            }),
            PUT_LINE: (arg) => new Promise((res) => {
              setTimeout(() => {
                log(arg);
                res("");
                render();
              });
            })
          }).then(() => {
            log("");
            render();
          });
        } catch (e) {
          log_error(e);
        }
        break;
      case "eval":
        log("Evaluating `" + argument + "`:", true);
        try {
          var norm = FL.norm(get_expr(argument), state.defs, true);
          log(FL.show(FL.erase(norm)));
        } catch (e) {
          try {
            var norm = FL.norm(get_expr(argument), state.defs, false);
            log("Possibly infinite term. Weak head normal form:");
            log(FL.show(FL.erase(norm)));
          } catch (e) {
            log("Possibly infinite term. No weak head normal form found.");
            log_error(e);
          }
        }
        log("");
        break;
      case "ipfs-save":
        log("Saving to IPFS disabled temporarily.", true);
        break;
      case "ipfs-load":
        log("Loading term.", true);
        var code = window.prompt("IPFS temporarily disabled. Enter code manually:");
        var defs = FL.parse(FS.desugar(code));
        Object.assign(state.defs, defs);
        log("Loaded `" + Object.keys(defs).length + "` definition(s).");
        log("");
        break;
      default:
        log("Command `" + action + "` not found.", true)
        log("Type `help` for a list of commands.");
        log("");
        break;
    }
  }

  document.onkeydown = (e) => {
    if (document.activeElement.id !== "code-editor" && !e.metaKey && !e.ctrlKey) {
      if (e.key === "Enter") {
        execute(state.inpt);
        state.inpt = "";
      } else if (e.key === "Backspace") {
        state.inpt = state.inpt.slice(0, -1);
      } else if (e.key.length === 1) {
        state.inpt += e.key;
      }
      render();
    }
  };

  document.onpaste = (e) => {
    if (document.activeElement.id !== "code-editor") {
      state.inpt += e.clipboardData.getData('text/plain');
      render();
    }
  };

  document.onkeyup = (e) => {
    if (document.activeElement.id === "code-editor") {
      state.code = code_editor.value;
      render();
    }
  }

  log("Welcome to Moonad!", true);
  log("Enter a command or `help` to get started.");
  log("");

  render();
};

window.onload = () => {
  install(document.getElementById("main"));
};
