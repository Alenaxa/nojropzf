(function () {
    "use strict"
    localStorage.setItem("noj_pid", "unknown");

    $(".hidden").hide();
    
    let alive= $('.live_stream');
    let count= $('.counter');
    let $npid = localStorage.getItem("noj_pid");
    let cookie = $npid ? true : false;
    
    $("#allowCookie").on("click", function(){
        localStorage.setItem("noj_pid", nojpzfjs.newNpid());
        $('.cookie_alert').hide();
    });
    
    
    if (cookie) {
        $('.cookie_alert').hide();
    }else{
        $('.cookie_alert').show();
    }
    
    $('.copyPZF').on('click', function() {
        var $this = $(this);
        var copyContent = $this.attr('copy-pzf') ? $this.attr('copy-pzf') : $this.text();
        navigator.clipboard.writeText(copyContent);
        //$this.removeClass("fa-copy");
        $this.addClass("fa-check-circle text-success");
        $this.removeClass("fa-check-circle text-success");
        $this.hide(50);
        $this.show(150);
    });
    
    $(".walletPZF").on('click', function() {
        var $this = $(this);
        here.show();
    });

    $(".closeCtap").on('click', function(){
        var $this = $(this);
        var Did = $this.attr('cap-id');
        $('#' + Did +'').hide();
    });

    $('.pzf_pending_open').on('click', function() {
        $('.pzf_pending_open').toggleClass('fadeOut');
        $('.pzf_pending_tab').toggleClass('active');
    });
    
    $('.pzf_pending_close').on('click', function() {
        $('.pzf_pending_tab').removeClass('active');
        $('.pzf_pending_open').removeClass('fadeOut');
    });
    
    
    if(count.length){
        count.counterUp({
            delay: 50,
            time: 1000
        });
    }
    
    if(alive.length){
        alive.counterUp({
            delay: 50,
            time: 1000
        });
    }
    
    function update_stream(argument) {
        if(alive.length){
            alive.counterUp({
                delay: 50,
                time: 1000
            });
        }
    }
    
    setInterval(function(){
        update_stream();
    }, 5000);
})();