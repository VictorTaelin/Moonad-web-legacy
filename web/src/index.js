import prelude from './prelude.formality';

const S = require("./moonad-store-api");
const F = require("formality-lang");
const I = require("nano-ipfs-store").at("https://ipfs.infura.io:5001"); 

function install(main) {
  var state = {
    play: null,
    defs: F.parse(prelude),
    input: "",
    log: []
  };

  function log(value, bold = false) {
    state.log.push({value, bold});
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
      //element.innerText = text;
      return element;
    }

    main.innerHTML = "";
    main.style.width = "100%";
    main.style.height = "100%";
    main.style.fontFamily = "'Anonymous Pro', 'Courier New', monospace";
    main.style.fontSize = 14 + "px";
    main.style.overflowX = "hidden";
    main.style.overflowY = "auto";

    if (!state.play) {
      for (var i = 0; i < state.log.length; ++i) {
        if (typeof state.log[i].value === "string") {
          var line = Line(state.log[i].value || ".");
          line.style.fontFamily = "inherit";
          line.style.fontSize = "inherit";
          line.style.visibility = !state.log[i].value ? "hidden" : null;
          line.style.textDecoration = state.log[i].bold ? "underline" : null;
          main.appendChild(line);
        } else {
          main.appendChild(state.log[i].value);
        }
      }
      main.appendChild(Line("> " + state.input));
    } else {
    }

    main.scrollTop = main.scrollHeight;
  }

  function get_expr(expr) {
    return F.parse("tmp_expr = " + "(" + (expr || "main") + ")").tmp_expr.term;
  }

  function execute(command) {
    var split_index = command.indexOf(" ");
    var split_index = split_index === -1 ? command.length : split_index;
    var action = command.slice(0, split_index);
    var argument = command.slice(split_index + 1);
    switch (action) {
      case "help":
        log("Available commands:", true);
        log("list <term>  : list available terms");
        log("show <term>  : displays the term");
        log("eval <term>  : evaluates a term to normal form");
        log("check <term> : checks the type of a term");
        log("save         : saves the program on IPFS");
        log("load <hash>  : loads a program from IPFS");
        log("clear        : clears the console");
        log("play <term>  : runs a Formality App");
        log("");
        break;
      case "list":
        for (var name in state.defs) {
          log("- " + name);
        }
        log("");
        break;
      case "clear":
        state.log = [];
        state.apps = [];
        break;
      case "show":
        log("Showing `" + argument + "`:", true);
        log(F.show(state.defs[argument].term));
        log("");
        break;
      case "check":
        try {
          log("Checking `" + argument + "`:", true);
          log(F.show(F.infer(get_expr(argument), state.defs)));
          log("");
        } catch (e) {
          e.split("\n").forEach(log);
        }
        break;
      case "eval":
        log("Evaluating `" + argument + "`:", true);
        try {
          var norm = F.norm(get_expr(argument), state.defs, true);
          log(F.show(F.erase(norm)));
        } catch (e) {
          try {
            var norm = F.norm(get_expr(argument), state.defs, false);
            log("Possibly infinite term. Weak head normal form:");
            log(F.show(F.erase(norm)));
          } catch (e) {
            log("Possibly infinite term. No weak head normal form found.");
            console.log(e);
          }
        }
        log("");
        break;
      case "save":
        log("Function disabled temporarily.");
        break;
        //log("Saving code to IPFS...");
        //I.add(state.code)
          //.then((hash) => {
            //log("Code saved. Hash: `" + hash + "`.");
            //render();
          //})
          //.catch((e) => console.log(e));
        //break;
      case "load":
        log("Function disabled temporarily.");
        break;
        //log("Loading code from IPFS...");
        //I.cat(argument).then((code) => {
          //state.code = code;
          //log("Done!");
          //render();
        //})
        //.catch((e) => console.log(e));
        //break;
      case "play":
        log("Function disabled temporarily.");
        break;
        //var term = F.Ref(argument || "main");
        //log("Playing `" + term[1].name + "`.");
        //try {
          //F.check(term, F.App(false, F.Ref("App"), term), defs);
        //} catch (e) {
          //log("Error: `"+term[1].name+"` isn't a App.");
        //}
        //var init = F.App(false, F.Ref("App.init"), term);
        //var next = F.App(false, F.Ref("App.next"), term);
        //var draw = F.App(false, F.Ref("App.draw"), term);
        //var st = F.norm(init, defs);
        //var app = document.createElement("canvas");
        //app.width = 256;
        //app.height = 256;
        //app.style.width = "128px";
        //app.style.height = "128px";
        //app.getContext("2d").scale(2,2);
        //app.state = F.norm(init, defs);
        //app.style.border = "1px solid black";
        //app.style.marginTop = "6px";
        //app.style.marginBottom = "6px";
        //app.selected = true;
        //app.render = () => {
          //var ctx = app.getContext("2d");
          //var bits = term_to_bitstring(F.norm(F.App(false, draw, app.state), defs));
          //ctx.textAlign = "center";
          //ctx.textBaseline = "middle";
          //ctx.clearRect(0, 0, app.width, app.height);
          //ctx.font = "12px Courier New";
          //ctx.fillText(parseInt(bits || "0", 2), 64, 64);
          //app.style.border = app.selected ? "2px solid #8888FF" : "1px solid black";
        //}
        //app.onclick = () => {
          //app.selected = !app.selected;
          //app.render();
        //}
        //app.key = (key) => {
          //app.state = F.norm(F.App(false, F.App(false, next, F.Typ()), app.state), defs);
          //app.render();
        //}
        //app.render();
        //state.apps.push(app);
        //log(app);
        //break;
      default:
        execute("eval " + command);
        break;
    }
  }

  document.onkeydown = (e) => {
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

  log("Welcome to Moonad!", true);
  log("Enter a command or `help` to get started.");
  log("");

  render();
};

window.onload = () => {
  install(document.getElementById("main"));
};
