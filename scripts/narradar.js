/*
function sendForm(){
  new Ajax.Request('/cgi-bin/narradar', {
      method: 'post',
      parameters: $('form').serialize(true),
      onSuccess: function(transport){
	  $('canvas').innerHTML = transport.responseText;
	  $('formDiv').hide();
	  $('goBack').show();
      }});
}
  */

function restart(){
    $('#formDiv').show();
    $('#canvas')[0].innerHTML = "";
    $('#goBack').hide();}

function narradar_init() {
    $(document).ready(function() {
	$('#myform').ajaxForm({target:'#canvas',success: showProofs});
    });
    $().ajaxStart(function(){$.blockUI({ css: { 
        border: 'none', 
        padding: '15px', 
        backgroundColor: '#000', 
        '-webkit-border-radius': '10px', 
        '-moz-border-radius': '10px', 
        opacity: '.5', 
        color: '#fff' 
     }})});
    $().ajaxStop($.unblockUI);
}
		     
function showProofs(responseText, statusText) {
//	  $('#canvas').innerHTML = responseText;
	  $('#formDiv').hide();
	  $('#goBack').show();
    tb_init('a.thickbox');
}