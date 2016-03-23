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


$(document).ready(function() {
    // Handler for upload of PRISM
    $("#upload-prism").submit(function(event){
        event.preventDefault();

        var formData = new FormData($(this)[0]);
        doAjax({
            url: '../uploadPrism',
            type: 'POST',
            // Form data
            data: formData,
            //Options to tell jQuery not to process data or worry about content-type.
            cache: false,
            contentType: false,
            processData: false
        }, function(){
            listFilesForManager();
        });
    });

    // Handler for upload of PCTL
    $("#upload-pctl").submit(function(event){
        event.preventDefault();

        var formData = new FormData($(this)[0]);
        doAjax({
            url: '../uploadPctl',
            type: 'POST',
            // Form data
            data: formData,
            //Options to tell jQuery not to process data or worry about content-type.
            cache: false,
            contentType: false,
            processData: false
        }, function(){
            listFilesForManager();
        });
    });

    // Handler for upload of result
    $('#upload-result').submit(function(event){
        event.preventDefault();

        var formData = new FormData($(this)[0]);
        formData.append("result-type","storm"); // WARNING: HARD CODED
        doAjax({
            url: '../uploadResult',
            type: 'POST',
            // Form data
            data: formData,
            //Options to tell jQuery not to process data or worry about content-type.
            cache: false,
            contentType: false,
            processData: false
        }, function() {
            listFilesForManager();
        });
    });

    $("#upload-pctl-manual").submit(function(event){
        event.preventDefault();

        var formData = new FormData($(this)[0]);
        doAjax({
            url: '../uploadFormula',
            type: 'POST',
            // Form data
            data: formData,
            //Options to tell jQuery not to process data or worry about content-type.
            cache: false,
            contentType: false,
            processData: false
        }, function(){
            listFilesForManager();
        });
    });

    $("#pctl-groups").on('change', function(){
            if($("#pctl-groups").val()=="addNew"){
                $("#add-group").css("display","inline");
            }
            else{
                $("#add-group").css("display","none");
            }

        });

    // Load the groups to select
    listPCTLGroups();

    listFilesForManager();
});


function listPCTLGroups() {
    doJSON("../uploadPctl", function(result){
        var hSelect = $("#pctl-groups");
        var groups = result.data.pctl;
        hSelect.empty();
        for (var groupname in groups){
            hSelect.append($('<option>', {
                value: groupname,
                text: groupname
                }));
        }
        hSelect.append($('<option>', {
                value: "addNew",
                text: "New Group"
                }));
        });
}