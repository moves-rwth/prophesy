function doJSON(url, onSuccess = function(result) {}, onFail = function() {}) {
    doAjax({
        dataType: "json",
        url: url,
    }, onSuccess, onFail);
}

function doAjax(ajax, onSuccess = function(result) {}, onFail = function() {}) {
    failHandler = function(jqXHR) {
        try {
            return $.parseJSON(jqXHR.responseText);
        } catch(err) {
            return null;
        }
    }

    $.ajax(ajax)
    .done(function(data) {
        if (data.status == "ok") {
            onSuccess(data);
        }
    })
    .fail(function(jqXHR) {
        onFail();
    })
}

function getConfig(section, key){
    doJSON("../config/"+section+"/"+key, function(result) {
        $("#"+key).val(result.data);
    });
}

function setConfig(section, key, data){
    var formData = new FormData();
    formData.append('data',$("#"+data).val());
    doAjax({
        url: '../config/'+section+'/'+key,
        type: 'POST',
        data: formData,
        cache: false,
        contentType: false,
        processData: false
    });
}

$(document).ready(function() {

    doJSON("../config", function(result) {
        jQuery.each(result.data, function(section, keys) {
            jQuery.each(keys, function(key, value) {
                $("#" + section).append("<input type=\"text\" id=\""+key+"\" value=\""+value+"\">"+key+"</input>");
                });
        });
    });

    $("#configchange").click(function(event){
        event.preventDefault();
        doJSON("../config", function(result) {
        jQuery.each(result.data, function(section, keys) {
            jQuery.each(keys, function(key, value) {
                setConfig(section, key, key);
            });
        });
    });
    });

});