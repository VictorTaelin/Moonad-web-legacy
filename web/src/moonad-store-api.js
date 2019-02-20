const R = require("xhr-request-promise");

// Gets the href url to perform a call on the store
function href() {
  return window.location.protocol + "//" + window.location.hostname + ":8001/";
}

// Retrieves a term from the store
function save(name, value) {
  var url = href() + name;
  var obj = {value, admin_key: window.ADMIN_KEY || "0123456789abcdef"};
  var arg = {method: "PUT", json: true, body: obj};
  return R(url, arg)
    .then((result) => (console.log(result), result[0] === "success"));
}

// Saves a term on the store
function load(name) {
  return R(href() + name, {method: "GET", json: true})
    .then((result) => result[0] === "success" ? JSON.parse(result[1]) : null);
}

module.exports = {save, load};
