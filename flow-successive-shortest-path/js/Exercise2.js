/**
 * @author Gergana Kratuncheva
 * Code fuer Forschungsaufgabe 2<br>
 * Basiert auf dem Code für den normalen Algorithmus
 */
/**
 * Instanz der Forschungsaufgabe 2
 * @constructor
 * @param {BipartiteGraph} p_graph Graph, auf dem der Algorithmus ausgeführt wird
 * @param {Object} p_canvas jQuery Objekt des Canvas, in dem gezeichnet wird.
 * @param {Object} p_tab jQuery Objekt des aktuellen Tabs.
 * @augments GraphDrawer
 */
function Exercise2(svgSelection) {
    //FordFulkersonAlgorithm.call(this, svgSelection);
    GraphDrawer.call(this, svgSelection, null, null, "tf2");

    var svgOrigin = d3.select("body")
        .select("svg");
    var svg = d3.select("#tf2_canvas_graph");
    this.svgOrigin
        .on("mousedown", mousedown);
    // event handler for enter key
    d3.select("body")
        .on("keydown", function() {
            var key = d3.event.keyCode;
            if(key == 13) { // enter key code
                mousedown();
            }
        });


    //insert markers
    var definitions = svgSelection.append("defs")
        .attr("id", "line-markers");

    definitions.append("marker")
        .attr("id", "flow-arrow1")
        .attr("refX", 12) /*must be smarter way to calculate shift*/
        .attr("refY", 2)
        .attr("markerWidth", 12)
        .attr("markerHeight", 4)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M 0,0 V 4 L6,2 Z")
        .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead

    definitions.append("marker")
        .attr("id", "residual-forward1")
        .attr("refX", 14) /*must be smarter way to calculate shift*/
        .attr("refY", 3)
        .attr("markerWidth", 14)
        .attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M 2,3 L0,6 L8,3 Z")
        .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead

    definitions.append("marker")
        .attr("id", "residual-backward1")
        .attr("refX", 0) /*must be smarter way to calculate shift*/
        .attr("refY", 3)
        .attr("markerWidth", 14)
        .attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M 6,3 L12,3 L14,0 Z")
        .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead





    /**
     * Closure Variable für dieses Objekt
     * @type Forschungsaufgabe1
     */
    var that = this;
    var algo = that;


    var currentFlow = 0;
    var minCost = 0;
    var debugConsole = true;

	var selectedNodes = new Array();
	var selectedEdges = new Array();
    var geantwortet = 0;

	
	
    /**
     * Parameter der aktuellen Frage (wird dann für die Antwort verwendet)<br>
     * frageKnoten: Knoten, zu dem die Frage gestellt wurde<br>
     * Antwort : String der richtigen Antwort<br>
     * AntwortGrund: Begründung der richtigen Antwort<br>
     * newNodeLabel: Label den der Knoten nach der richtigen Beantwortung bekommt (neuer Abstandswert)<br>
     * gewusst: Ob die Antwort bereits beim ersten Versuch korrekt gegeben wurd<br>
     * @type Object
     */
    this.frageParam = new Object();

    var tabVorfrage = null;
    /**
     * Statistiken zu den Fragen
     * @type Object
     */
    var frageStats = {
        richtig: 0,
        falsch: 0,
        gestellt: 0
    };
	/**
	* Boolean variable that shows if question 1 is active. Used to separate the questions by handling the answers.
	*/
	var askquestion1 = false;
	
		
	/**
	* Boolean variable that shows if question 2 is active. Used to separate the questions by handling the answers.
	*/
	var askquestion2=false;
	
	/**
     * Status der Frage.<br>
     * Keys: aktiv, warAktiv
     * Values: Boolean
     * @type Object
     */
    var frageStatus = new Object();
	
    /**
     *  Die nextStepChoice Methode der Oberklasse
     *  @type method
     */
    this.algoNext = this.nextStepChoice;

	var counter = 0;	
	
	/**
	*   The graph that was used the last time for this exercise
	*/
	var oldGraph = 0;
		/**
	*   A random chosen graph that will be used this time in 
	*   exercise (and will NOT be the same as the last time)
	*/
	var randomGraph = 0;
	var bs = new Array();
	var ps = new Array();



    var currentFlow = 0;
    var minCost = 0;
	var potentials = [];
	var b = [];

	var STEP_BEGINALGORITHM = 			"begin-algorithm";
    var STEP_SELECTSOURCE = 	    	"select-source";
    var STEP_SELECTTARGET =     		"select-target";
	var STEP_MAINLOOP =  			    "main-loop";
	var STEP_FINDSHORTESTPATH =			"find-shortestpath";
	var STEP_UPDATEPOTENTIALS = 		"update-potentials";
	var STEP_UPDATECOST = 				"update-cost";
	var STEP_APPLYPATH =        		"apply-augmentation-path";
	
	var STEP_START = 					"start-algorithm";
    var STEP_PREPARECOST =				"prepare-cost";
	var STEP_PREPAREPOTENTIALS = 		"prepare-potentials";
	
    var STEP_FINISHED = 				"finished";
	
	
	/**
     * the logger instance
     * @type Logger
     */
	var logger = new Logger(d3.select("#logger"));
	
	
	/** 
	* distance vector with predecessors and distances from s to every other node
	*/
	var distance = new Array();
	
	var del = 0;
	var maxFlow = 0;
	
	/**
	* vector with shortest path from s to t
	*/
	var shortestPath = new Array();
	
	/**
	* Array that contains all the edges in the shortest path
	*/
	var edgesOfSP = new Array();
	var answer4 = 0;
	var delta = 0;

	var bOfS =0;
	var bOfT =0;
	var usedUpNodes = new Array();
	var edgePrevCost = new Array();
	 /**
     * status variables
     * @type Object
     */
	 
	 var mainLoopCounter = 0;
	var edges = new Array();
	 
	 
	
	 /**
     * status variables
     * @type Object
     */
	 
    var state ={
      current_step: STEP_SELECTSOURCE, //status id
      sourceId: -1,
      targetId: -1,
      potentials: [],
	  b: [],
	  distance: [],
	  distancesOfNodes:[],
	  edgesOfSP: [],
	  edgePrevCost: [],
	  anotherEdgeRed: false,
      currentCost: 0
	  
    };
	
	
	var colormap = ["#a50026", "#d73027", "#f46d43", "#fdae61", "#fee08b", "#ffffbf", "#d9ef8b", "#a6d96a", "#66bd63", "#1a9850", "#006837"].reverse();

    function flowWidth(val) {
      var edges = Graph.instance.getEdges();
      var capacity = [];
      for (var i =0; i<edges.length; i++){
        capacity[i] = edges[i].resources[0];
      }
        var maxCap = d3.max(capacity);
        return Math.floor(25*(val/maxCap));
    }

    this.flowWidth = flowWidth;

    this.nodeLabel = function(d) {
        if (d.id == state.sourceId)
            return "s";
        else if (d.id == state.targetId)
            return "t";
        else
            return d.id;
    }

	
	
	
    this.nodeText = function(d){
		var res = "b: " + d.b;
		return res;
	};
	
	this.nodeText2 = function(d){
		var pAlternatives;	
		if(d.selected && d.addP){
			pAlternatives = "?";
		}else if($.inArray(d.id,selectedNodes) != -1){
			console.log("in else if ");
			pAlternatives = d.antwortP;		
		}else{			
			pAlternatives = d.p;			
		}
		var res = "p: " + pAlternatives;
		console.log(res);
		return res;
		
	};
	

	
    this.edgeText = function(d) {
		var cost = 0;
		
		if(d.selected)
			return "?";
		else if($.inArray(d,selectedEdges) != -1){
			if(typeof d.answerCost != 'undefined'){
				cost = d.answerCost;
				return "(" +d.state.flow + ", " +cost + ")";	
			}

				
		} 
		/*}else if($.inArray(d,selectedEdges) != -1 && typeof d.answerCost != 'undefined'){
			console.log("d.answerCost = " + d.answerCost + "d.answerCap = " + d.answerCap);

			cost = d.answeCost;
			resCap = 0;
			return "(" +resCap + ", " +cost + ")";
		
		}else if($.inArray(d,selectedEdges) != -1 && typeof d.answerCap != 'undefined'){
			console.log("3.else if");
			console.log("d.answerCost = " + d.answerCost + "d.answerCap = " + d.answerCap);
			cost = 0;
			resCap = d.answerCap;
			return "(" +resCap + ", " +cost + ")";	
		}else if($.inArray(d,selectedEdges) != -1){
			console.log("4.else if");
			console.log("d.answerCost = " + d.answerCost + " d.answerCap = " + d.answerCap);
		//	cost = 0;
		//	resCap = 0;
			return "(" +resCap + ", " +cost + ")";	
		}*/
			
		if(!state.show_residual_graph){
			if(d.resources[1]<0){
				cost = 0;
			}else if (typeof d.resources[1] != 'undefined'){
				cost = d.resources[1];
			}else if(typeof d.tempCost != 'undefined'){
				cost = d.tempCost;
			}
	
			return "("+d.state.flow+"/"+d.resources[0]+","+cost+")";
		}else{
			
			
			 if(d.resources[1]<0){
				cost = 0;
			}else{
				cost = d.resources[1];
			}
			if(d.state.flow < d.resources[0])
				return "(" +(d.resources[0] - d.state.flow) + ", " +cost + ")";
			else
				return "";
		}
		
    }

    this.edgeTextBelow = function(d) {
        if(state.show_residual_graph && d.state.flow > 0 && $.inArray(d,selectedEdges) == -1){
			var cost;			
			if(d.resources[1]<0){
				cost = 0;
			}else{
				cost = d.tempCost;
			}	
            return "(" + d.state.flow + ", " + cost + ")";
		
		}else
            return "";
    }
	
	
    this.onNodesEntered = function(selection) {
        //select source and target nodes
        selection
        .on("click", function(d) {
            if (state.current_step == STEP_SELECTSOURCE ||
                (state.current_step == STEP_SELECTTARGET && d.id != state.sourceId) )
            {
                that.nextStepChoice(d);
            }
        })

    }

    this.onNodesUpdated = function(selection) {
        selection
        .selectAll("circle")
        .style("fill", function(d) {
            
            if(d.b > 0)
				return const_Colors.StartNodeColor; //green for excess nodes
			else if(d.b < 0)
				return const_Colors.RedText; //red for demand nodes
			else if (d.id == state.sourceId)
                return const_Colors.PQColor; //gelb for start node
            else if (d.id == state.targetId)
                return const_Colors.PQColor;//gelb for end node
			else
                return global_NodeLayout['fillStyle'];

        })


    }



    this.onEdgesEntered = function(selection) {
         selection.append("line")
            .attr("class", "cap")           
			.style("stroke-width",
                    function(d)
                    {
                        return algo.flowWidth(d.resources[0]);
                    })
		 selection.append("line")
            .attr("class", "flow");
            //algo.onEdgesUpdated(selection);

    }

    this.onEdgesUpdated = function(selection) {
        selection.selectAll("line.flow")
            .style("stroke-width",
                function(d)
                {
					if(d.inSP)
						return 5;
					else
						return 0;
                });
	 selection.selectAll("line.cap")
           .style("stroke-width",
                 function(d)
                 {
                   if(d.inSP)
						return 5;
					else
						return 0;
				});


        selection.select(".arrow")
            .style("stroke",
                function(d)
                {
					if(d.inSP)
						return "#0000FF";
                    else
                        return "black";
                })

            .attr("marker-end",
                function(d){
                    if(!state.show_residual_graph)
                    {
                        return "url(#flow-arrow1)";
                    }
                    else
                    {
                        if(d.resources[0] - d.state.flow > 0)
                            return "url(#residual-forward1)";
                        else
                            return "";
                    }
                })
            .attr("marker-start",
                function(d){
                    if(!state.show_residual_graph)
                    {
                        return "";
                    }
                    else
                    {
                        if(d.state.flow > 0)
                            return "url(#residual-backward1)";
                        else
                            return "";
                    }
                });


        selection.selectAll("line.cap")
            .style("visibility",
                function()
                {
                    return state.show_residual_graph ? "visible" : "hidden";
                });
        selection.selectAll("line.flow")
            .style("visibility",
                function()
                {
                    return state.show_residual_graph ? "visible": "hidden";
                });



    }

	/**
     * Replay Stack, speichert alle Schritte des Ablaufs für Zurück Button
     * @type {Array}
     */
    var replayHistory = new Array();

    var fastforwardOptions = {label: $("#ta_button_text_fastforward").text(), icons: {primary: "ui-icon-seek-next"}};

     /**
     * Initialisiert das Zeichenfeld
     * @method
     */
    this.init = function() {
        console.log("init in Exercise2");
        Graph.addChangeListener(function() {
            that.clear();
            that.reset();
            that.squeeze();
            that.update();
        });

        this.reset();
        this.update();
        if(Graph.instance) {
			
            Exercise2.prototype.update.call(this); //updates the graph
        }


    };
	
	
	var initialCost = new Array();
	
    /**
     * clear all states
     */
    this.reset = function(){
        state = {
			current_step: STEP_BEGINALGORITHM, //status id
			sourceId: -1,
			targetId: -1,
			shortestPath: [],
			distance: [],
			distancesOfNodes:[],
			edgePrevCost: [],
			anotherEdgeRed: false,
			currentCost: 0
        };
		oldGraph = randomGraph;
		usedUpNodes = new Array();
		del=0;
		count = 0;
		geantwortet = 0;
		selectedNodes = [];
		selectedEdges = [];
		edgesOfSP = new Array();
		distance = new Array();
		mainLoopCounter =0;
		edges = new Array();
       // logger.data = [];
        this.replayHistory = [];
        this.currentFlow= 0;
        this.minCost = 0;
        if(Graph.instance){
            //prepare graph for this algorithm: add special properties to nodes and edges
            Graph.instance.nodes.forEach(function(key, node) {
                node.state.predecessor = null;
                node.b = 0;
				node.p = 0;
				bs[node.id] = node.b;
				ps[node.id] = node.p;
				node.isUsedUp = false;
            })

            Graph.instance.edges.forEach(function(key, edge) {
                edge.state.flow = 0;
				edge.inSP = false;
				edge.state.usedUp = false;
				if(mainLoopCounter >1){
					edge.resources[1] = initialCost[edge.id];
					
				}
            });

        }
    }
	
	
	this.update = function() {

        this.updateDescriptionAndPseudocode();
        this.updateVariableState();
        this.updateGraphState();


        logger.update();

        if(Graph.instance) {
            //  console.log("Upadte Graph!")
            Exercise2.prototype.update.call(this); //updates the graph
        }
    };
	
	/**
     * updates status description and pseudocode highlight based on current step
     * @method
     */
     this.updateDescriptionAndPseudocode = function() {
        var sel = d3.select("#tf2_div_statusPseudocode")
            .selectAll("div");
        sel.classed("marked", function(a, pInDivCounter, divCounter) {
            return d3.select(this)
                .attr("id") === "fr2-pseudocode-" + state.current_step;
        });

        var sel = d3.select("#tf2_div_statusErklaerung")
            .selectAll("div");
        sel.style("display", function(a, divCounter) {
            return(d3.select(this)
                .attr("id") === "fr2-explanation-" + state.current_step) ? "block" : "none";
        });

        var disable_forward_button =
            (state.current_step === STEP_BEGINALGORITHM || state.current_step === STEP_SELECTSOURCE ||
                state.current_step === STEP_SELECTTARGET ||
                state.current_step === STEP_FINISHED || frageStatus.aktiv);
       

        $("#tf2_button_1Schritt")
            .button("option", "disabled", disable_forward_button);
	
    };


    this.updateGraphState = function()
    {
        var state_label = "";
        var currMinCost = "";
        if(state.show_residual_graph){
            state_label = "Residual network";
        }else{
          state_label = "Network"
        }
       /* if(state.current_step == STEP_FINISHED){
          currMinCost = "Minimal cost: " + minCost;
        }else{
          currMinCost = "Current cost: " + minCost;
        }*/
        d3.select("#f2-graph-state").text(state_label);
       /* d3.select("#cost-info").text(currMinCost)
        d3.select("#graph-info").style("display", state.show_residual_graph ? "block" : "block");*/
    }
	
    this.updateVariableState = function()
    {	
		
        var sp_edge_strings = [];
        console.log("updateVar shortestPath: " + state.shortestPath);
        for(var i = 0; i<state.shortestPath.length-1; i++){

            var edge_string = "";
            if(state.shortestPath[i] == state.sourceId)
                edge_string+= "s";
            else if(state.shortestPath[i] == state.targetId)
                edge_string += "t";
            else
                edge_string += state.shortestPath[i];

            edge_string += "->"

            if(state.shortestPath[i+1] == state.sourceId)
                edge_string += "s";
            else if(state.shortestPath[i+1] == state.targetId)
                edge_string += "t";
            else
                edge_string += state.shortestPath[i+1];

            sp_edge_strings.push(edge_string);
        }
        var sp_string = "["+sp_edge_strings.join(",")+"]";
		var distances_string = "("+state.distancesOfNodes.join(",")+")";
		console.log("sp_string: " + sp_string);
        d3.select("#variable-value-shortestPath").text(sp_string);
		d3.select("#variable-value-delta").text(del);
		d3.select("#variable-value-distances").text(distances_string);
        //d3.select("#variable-value-adjustment").text(delta);
        d3.select("#finalflow").text(maxFlow);
        d3.select("#minCost").text(minCost);
		d3.select("#bs").text(bOfS);
		d3.select("#bt").text(bOfT);
		//d3.select("#value-shortestPath").text(sp_string);

    }
	
     /**
         * When Tab comes into view
         * @method
         */
    this.activate = function() {

		$("#tf2_button_Retry").hide();
		Graph.instance.edges.forEach(function(key,edge){
			initialCost[edge.id] = edge.resources[1];
		});
		this.chooseRandomGraph(9);
		console.log("random graph " +randomGraph);
        Graph.setGraph("tf2");
		Graph.loadInstance("graphs-new/Ex2/graph"+ randomGraph + ".txt");
        this.stopFastForward();
        this.clear();
        this.squeeze();
        Exercise2.prototype.update.call(this);	
		
		
        /*this.reset();
        this.squeeze();
        this.update();*/
		 $("#tf2_canvas_graph")
            .attr("visibility", "hidden");
        this.removeResultsTab();
		

        // $(".marked").removeClass("marked");
        // $("#tf2_p_l1").addClass("marked");

        
		//$("#tf2_graphSelector").show();
        $("#tf2_button_start").show();
        $("#f2_started").hide();
        $("#tf2_button_1Schritt").button("option", "disabled", true);
        $("#tf2_button_vorspulen").button("option", "disabled", true);


        this.reset();
        this.squeeze();
        this.update();


        this.removeFrageTab();
        this.removeResultsTab();
        this.resetExercise();
        
		
		randomGraph = this.chooseRandomGraph(9);

        Graph.instance.edges.forEach(function(key, edge) {
            edge.state.flow = 0;
        });
		this.clear();
		this.reset();
		this.update();
		d3.select("body")
            .on("mousemove", that.registerEventHandlers);
		this.nextStepChoice();
		
        

    };

    this.refresh = function() {
        that.activate();
    }


    /**
     * tab disappears from view
     * @method
     */
    this.deactivate = function() {
        if(frageStatus.aktiv || frageStatus.warAktiv) {
            that.removeFrageTab();
        }
		Graph.instance.edges.forEach(function(key,edge){
			
			edge.resources[1] = initialCost[edge.id];
			
		});
		this.reset();
		Graph.instance.nodes.forEach(function(key,node){
			node.state.distance = Number.MAX_SAFE_INTEGER;
		});
		minCost = 0;
		oldGraph = randomGraph;
		
        this.removeResultsTab();
		
        this.stopFastForward();
        this.reset();
        this.clear();
        this.replayHistory = [];
		
        Graph.instance = null;
        // load selected graph again 
        Graph.setGraph("tg");
		this.reset();
    };

    this.resetExercise = function() {
       
        $("#tf2_button_start")
            .show();
        $("#f2-start")
            .show();
		
		oldGraph = randomGraph;
		
        this.frageParam = new Object();
        frageStats = {
            richtig: 0,
            falsch: 0,
            gestellt: 0
        };
    }
	
	 this.beginAlgorithm = function() {
		
		 $("#tf2_button_start")
            .click(
                function() {
                    $("#tf2_button_start").hide();
                    $("#f2-start").hide();
                    $("#f2_started").show();
						randomGraph = that.chooseRandomGraph(9);
						that.stopFastForward();
						that.clear();
						that.reset();
						that.update();
						
						that.squeeze();
						Exercise2.prototype.update.call(that);	
					//}
					
                   $("#tf2_button_1Schritt")
						.button("option", "disabled", true);

                    $("#tf2_canvas_graph")
                        .attr("visibility", "visible");
					Graph.instance.edges.forEach(function(key,edge){
						initialCost[edge.id] = edge.resources[1];
					});
                    state.current_step = STEP_SELECTSOURCE;
                    that.squeeze();
					console.log("squeeze 2");
                    
					
				});
    }
	
	
	
	///////////////////////Actual algorithm steps

    /**
     * Executes the next step in the algorithm
     * @method
     */
    this.nextStepChoice = function(d)
    {
		
        if (debugConsole)
            console.log("State Before: " + state.current_step);


        if(frageStatus.aktiv) {
            this.stopFastForward();
        }

        if(!frageStatus.aktiv) {
            if(frageStatus.warAktiv) {
                this.removeFrageTab();
                frageStatus.warAktiv = false;
            }		
		
        switch (state.current_step) {
			case STEP_BEGINALGORITHM:
                frageStatus = {
                    "aktiv": false,
                    "warAktiv": false
                };
				this.beginAlgorithm();
            case STEP_SELECTSOURCE:
                this.selectSource(d);
                break;
            case STEP_SELECTTARGET:
                this.selectTarget(d);
                break;
            case STEP_START:
				minCost = 0;
                logger.log("Now the algorithm can start");
                state.current_step = STEP_MAINLOOP;
				state.show_residual_graph = true;
				getMaxFlow();			
                break;
			case STEP_MAINLOOP:
				mainLoop();
				break;
			case STEP_FINDSHORTESTPATH:
                findShortestPath();
                break;
			case STEP_PREPAREPOTENTIALS:
				warnPotentials();
				break;
            case STEP_UPDATEPOTENTIALS:
                updatePotentials();
                break;
			case STEP_PREPARECOST:
				warnCost();
				break;
            case STEP_UPDATECOST:
                updateCost();		
                break;
            case STEP_APPLYPATH:
                applyPath();
                break;
            case STEP_FINISHED:
				this.endAlgorithm();
                this.stopFastForward();
                break;
            default:
                console.log("Fehlerhafter State");
                break;
			}
			if (debugConsole)
				console.log("State After: " + state.current_step);

			//update view with status values
			this.update();
		}
    };

	/**
     * select the source node
     */
    this.selectSource = function(d)
    {
        state.sourceId = d.id;
        state.current_step = STEP_SELECTTARGET;
        logger.log("selected node " + d.id + " as source");
    };

    /**
     * select the target node
     */
    this.selectTarget = function(d)
    {
        state.targetId = d.id;
        state.current_step = STEP_START;
        logger.log("selected node " + d.id + " as target");
    };
	
	
	 /**
	* Initializes maximal Flow and stores it in the variable currentFlow which is then used to initialize the excess/demand of the nodes s and t.
	*/
    function getMaxFlow()
    {

        Graph.instance.edges.forEach(
            function(key, edge)
            {
                edge.state.flow = 0;
            })

        var no_path_found = false;
        currentFlow = 0;
        while(!no_path_found)
        {
            Graph.instance.nodes.forEach(
                function(key, node)
                {
                    node.state.predecessor = null;
                });

            var search_queue = [state.sourceId];
            var source = Graph.instance.nodes.get(state.sourceId);
            source.state.predecessor = {};
            while(Graph.instance.nodes.get(state.targetId).state.predecessor == null && search_queue.length > 0 )
            {
                var node_to_expand = search_queue.shift();
                var node = Graph.instance.nodes.get(node_to_expand);
                var out_edges = node.getOutEdges();
                for (var i = 0; i < out_edges.length; i++)
                {
                    var edge_out = out_edges[i];

                    if(edge_out.end.state.predecessor == null && edge_out.resources[0] > edge_out.state.flow)
                    {
                        search_queue.push(edge_out.end.id);
                        edge_out.end.state.predecessor =
                            {
                                "node": node_to_expand,
                                "edge": edge_out.id,
                                "residual-capacity":edge_out.resources[0] - edge_out.state.flow,
                                "direction": 1
                            };
                    }
                }

                var in_edges = node.getInEdges();
                for (var i = 0; i < in_edges.length; i++)
                {
                    var edge_in = in_edges[i];

                    if(edge_in.start.state.predecessor == null && edge_in.state.flow > 0)
                    {
                        search_queue.push(edge_in.start.id);
                        edge_in.start.state.predecessor =
                            {
                                "node": node_to_expand,
                                "edge": edge_in.id,
                                "residual-capacity": edge_in.state.flow,
                                "direction": -1
                            };
                    }
                }
            }

            if(Graph.instance.nodes.get(state.targetId).state.predecessor != null)
            {
                var path = [];
                var augmentation = Number.MAX_SAFE_INTEGER;
                var next_path_node = state.targetId;

                //gather path
                while(next_path_node != state.sourceId)
                {
                    var node = Graph.instance.nodes.get(next_path_node);
                    path.push(node.state.predecessor);
                    augmentation = Math.min(node.state.predecessor["residual-capacity"], augmentation);
                    next_path_node = node.state.predecessor["node"];
                }

                //apply path
                for (var i = 0; i < path.length; i++)
                {
                    var predecessor = path[i];
                    var edge = Graph.instance.edges.get(predecessor["edge"]);
                    edge.state.flow += predecessor["direction"] * augmentation;

                }
                currentFlow += augmentation;


            }
            else
                no_path_found = true;
        }
		maxFlow = currentFlow;
        Graph.instance.nodes.forEach(
            function(key, node){
				bs[node.id] = node.b;
                if(node.id == state.sourceId){
					node.b = currentFlow;
					bOfS = node.b;
				}else if(node.id == state.targetId){
					node.b = -currentFlow;
					bOfT = node.b;
				}else{
					node.b = 0;
				}
			});
			
			Graph.instance.edges.forEach(
            function(key, edge)
            {
                edge.state.flow = 0;
            })

        var no_path_found = false;
        currentFlow = 0;
        state.current_step = STEP_MAINLOOP;
        logger.log("Init of maxflow.");

    }

	
	/**
	* main loop: checks if s is still an exces node. 
	*			 If if is: run the loop steps; 
	*		     If it is not: the algorithm terminates.
	* @method	
	*/
    function mainLoop()
    {
		mainLoopCounter++;
        if (Graph.instance.nodes.get(state.sourceId).b === 0) {
			state.current_step = STEP_FINISHED; //so that we display finished and not mainloop when done
			that.endAlgorithm();
            that.stopFastForward();
            
            logger.log("Finished with a min cost of "+ minCost);


        }
        else
        {
            logger.log("Not finished, starting search for augmentation cycle ");
            state.show_residual_graph = true;
            state.current_step = STEP_FINDSHORTESTPATH;
            
		
        }
    }
		
		
		
	/**
	* Implementation of the Bellman-Ford algorithm. 
	* Finds the shortest distances from s to every node in the graph and the shortest path from s to t.
	* @method
	*/
	function findShortestPath(){
		state.edgesOfSP = [];
		state.shortestPath = [];
		
		
		Graph.instance.nodes.forEach(
            function(key, node)
            {
								
					node.state.distance = Number.MAX_SAFE_INTEGER;
					node.state.predecessor = null;
            });

        var target  = Graph.instance.nodes.get(state.targetId);
        target.state.distance = Number.MAX_SAFE_INTEGER;
		var source  = Graph.instance.nodes.get(state.sourceId);
		source.state.distance = 0;
		source.state.predecessor = {
			"prev_node": state.sourceId,
			"direction": 1
		}

		var usedUpEdges=new Array();
	
		for(var i = 0; i < Graph.instance.nodes.size(); i++){
			Graph.instance.edges.forEach(function(key,edge){
				var edge_startnode = edge.start;
				var edge_endnode = edge.end;
	
					if(!edge.state.usedUp && edge_endnode.usedUp == false && edge_startnode.usedUp == false){
						
					
						if(edge.resources[0] - edge.state.flow > 0){
							if(edge.state.flow > 0){
								
								if(edge_endnode.state.distance - edge.state.cost < edge_startnode.state.distance){
									
									edge_startnode.state.distance = edge_endnode.state.distance - edge.resources[1];
									
									
									edge_startnode.state.predecessor = {
										"edge_id": edge.id*(-1)-1,
										"prev_node": edge_endnode.id,
										"direction": -1
									};
									console.log("node "+ edge_startnode.id + " with predecessor " + edge_startnode.state.predecessor["prev_node"]);
								}
								
							}
							if(edge_startnode.state.distance + edge.resources[1] < edge_endnode.state.distance){
								
								edge_endnode.state.distance = edge_startnode.state.distance + edge.resources[1];
		
								
								edge_endnode.state.predecessor = {
											"edge_id": edge.id,
											"prev_node": edge_startnode.id,
											"direction": 1
								};
								
								
										  
							}

						}
					}
						
			});
			Graph.instance.edges.forEach(function(key,edge){
				var edge_startnode = edge.start;
				var edge_endnode = edge.end;
				var numberOfUsedUp = 0;
				
					if (edge.state.usedUp){
						usedUpEdges.push(edge);
						var inE = edge_endnode.getInEdges();
	
						
						for(var i = 0; i<inE.length; i++){
							if(inE[i].state.usedUp){
								numberOfUsedUp++;
							}
						}
						

						if(numberOfUsedUp != inE.length){
							inE.filter(function(e){
								return !e.state.usedUp;
							});
							inE.sort(function(a,b){
									return (a.resources[1]) - (b.resources[1]);
							});
							
							
							var e;
							var id=-1;
							for(var i = 0; i<inE.length; i++){
						
								if(inE[i].start.predecessor == null){

									inE[i].start.state.distance = 0;
									inE[i].start.state.predecessor = {
										"edge_id" : inE[i].id,
										"prev_node": inE[i].start.id,
										"direction" : 1
									}	
									
									
								}
								
								if(!inE[i].state.usedUp && inE[i].start.state.predecessor["direction"] == 1){
									id = i;	
									e = inE[id];
									break;
								}
							}
							if(id != -1){
						
								edge_endnode.state.distance = edge_startnode.state.distance + e.resources[1];
								edge_endnode.state.predecessor = {
											"edge_id": e.id,
											"prev_node": inE[id].start.id,
											"direction": 1
								}
								
							}else{
								edge_endnode.state.distance = edge_startnode.state.distance + edge.resources[1];
								edge_endnode.state.predecessor = {
											"edge_id": edge.id,
											"prev_node": edge.start.id,
											"direction": 1
								}
								
							}
						}else{
							
							edge_endnode.usedUp = true;
							edge_endnode.state.distance = edge_startnode.state.distance + edge.resources[1];
							usedUpNodes.push(edge_endnode);
						}
						
					}		
			});

		}	
			
		//backtrack to find SP from s to t
		var temp = Graph.instance.nodes.get(state.targetId);	
		
		
		while(temp.id != state.sourceId && 
		$.inArray(state.sourceId, state.shortestPath.reverse()) != 0 &&
		temp.state.predecessor["prev_node"] != state.targetId){
			

			state.shortestPath.reverse();
			
			if($.inArray(temp.id, state.shortestPath) == -1){

						var inEdgesForTemp = temp.getInEdges();
						
						for(var k = 0; k<inEdgesForTemp.length; k++){
							
							var tempSP = state.shortestPath;
						
							if(tempSP.filter(function(e) { return e == inEdgesForTemp[k].start.id; }).length > 0  || inEdgesForTemp[k].start.id == state.targetId ||  
							inEdgesForTemp[k].state.usedUp || 
							inEdgesForTemp[k].start.usedUp){
								
								inEdgesForTemp.splice(k,1);
							}
							
						}
						inEdgesForTemp.sort(function(a,b){
								
								return (a.start.state.distance + a.resources[1]) - (b.start.state.distance+b.resources[1]);
							
						});
						

						if(inEdgesForTemp.length == 0)
							return;
						else{
							temp.state.distance = inEdgesForTemp[0].start.state.distance + inEdgesForTemp[0].resources[1];
							temp.state.predecessor["prev_node"] = inEdgesForTemp[0].start.id;
							temp.state.predecessor["edge_id"] = inEdgesForTemp[0].id;
							temp.state.predecessor["diresction"] = 1;					
						}
			}
							

						state.shortestPath.unshift(temp.id);
					
					state.shortestPath.unshift(temp.state.predecessor["prev_node"]);
					var temp1 = temp;
					temp = Graph.instance.nodes.get(temp.state.predecessor["prev_node"]);
					
					if(temp.state.predecessor["prev_node"] == state.sourceId){
						
						state.shortestPath.unshift(temp.state.predecessor["prev_node"]);
						break;
					
					}else if($.inArray(temp.state.predecessor["prev_node"],state.shortestPath)!=-1 || 
							temp.state.predecessor["prev_node"] == temp1.id || 
							temp.state.predecessor["prev_node"] == state.targetId ||
							temp.state.predecessor["prev_node"]){
								
						
						var inEdgesForTemp = temp.getInEdges();
						
						for(var k = 0; k<inEdgesForTemp.length; k++){
		
							var tempSP = state.shortestPath;

							
							if(tempSP.filter(function(e) { return e == inEdgesForTemp[k].start.id; }).length > 0  || inEdgesForTemp[k].start.id == state.targetId ||  
							inEdgesForTemp[k].state.usedUp || 
							inEdgesForTemp[k].start.usedUp){
								
								inEdgesForTemp.splice(k,1);
							}
						}
						

						inEdgesForTemp.sort(function(a,b){

								return (a.start.state.distance + a.resources[1]) - (b.start.state.distance+b.resources[1]);
							
						});
						

						if(inEdgesForTemp.length == 0)
							return;
						else{
							temp.state.predecessor["prev_node"] = inEdgesForTemp[0].start.id;
							if(temp.state.predecessor["prev_node"] == state.sourceId){
								temp.state.distance = inEdgesForTemp[0].start.state.distance + inEdgesForTemp[0].resources[1];
								temp.state.predecessor["prev_node"] = inEdgesForTemp[0].start.id;
								temp.state.predecessor["edge_id"] = inEdgesForTemp[0].id;
								temp.state.predecessor["diresction"] = 1;
								state.shortestPath.unshift(temp.state.predecessor["prev_node"]);
								break;
							}
						}
						
					}	
					
		}
		
		Graph.instance.nodes.forEach(function(key,node){
			state.distancesOfNodes.push(node.state.distance);
		});

		for(var j = 1; j<state.shortestPath.length; j++){
			
			Graph.instance.edges.forEach(function(key,edge){
					if(edge.start.id == state.shortestPath[j-1] && edge.end.id == state.shortestPath[j]){
						edge.inSP = true;
						state.edgesOfSP.push(edge);
						edge.start.state.predecessor["direction"] = 1;
					}			
			});
		}
		
		state.current_step = STEP_PREPAREPOTENTIALS;
	}
	
	var selNodes = new Array();
	
	function warnPotentials(){
		
		that.addFrageTab();
        frageStatus.aktiv = true;
		
		$("#tf2_button_1Schritt")
            .button("option", "disabled", true);
		
		// Speichert zufaellige Knoten
		selNodes = new Array();
        var keys = [];
		 Graph.instance.nodes.forEach(function(nodeID, node) {
            keys.push(nodeID);
        });
		 var rand = Math.floor(Math.random() * (keys.length - 2));
		if(rand<2){
			rand = 2;
		}
        for(var i = 0; i < rand; i++) {
			
            selNodes.push(selectNode());
        }
		
		var selectedNodesString = "";
		for(var i = 0; i<selNodes.length; i++){
			if(selNodes[i] == state.sourceId){
				selectedNodesString += "s";
			}else if(selNodes[i] == state.targetId){
				selectedNodesString += "t";
			}else{
				selectedNodesString += selNodes[i];
			}
			
			if(i != selNodes.length-1){
				selectedNodesString += ",";
			}
			
		}
			
		$("#tf2_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe2_prepare_potentials') + "["+ selectedNodesString +"]"+  LNG.K('aufgabe2_click_ready') +"</p>");
		
		$("#tf2_div_Frage")
            .append("<br><p> </p><p>  </p><p>  </p><center><button id=\"tf2_button_READY\">Ready!</button> </center>");
			
		
		$("#tf2_button_READY")
            .button()
            .click(
                function() {
					that.removeFrageTab();
					updatePotentials();
                    that.askQuestion2();
					that.update();
                }
            );
		 
		

	}
	
	
	
	var selEdges = new Array();
	
	
	
	function warnCost(){
		that.addFrageTab();
		$("#tf2_button_1Schritt")
            .button("option", "disabled", true);
		frageStatus.aktiv = true;
		// Speichert zufaellige Kanten
		selEdges = new Array();
        var keys = [];
        Graph.instance.edges.forEach(function(edgeID, edge) {
            keys.push(edgeID);
        });
        var rand = Math.floor(Math.random() * (keys.length - 2)) + 2;

        for(var i = 0; i < rand; i++) {
            selEdges.push(selectEdge());
        }
				
		var selectedEdgesString = new Array();;
		
		for(var i = 0; i<selEdges.length; i++){
			var edgeString = "";
			if(selEdges[i].start.id == state.sourceId){
				edgeString += "s";
			}else{
				edgeString += selEdges[i].start.id;
			}
			
			edgeString += "-";
			
			if(selEdges[i].end.id == state.targetId){
				edgeString += "t";
			}else{
				edgeString += selEdges[i].end.id;
			}


            selectedEdgesString.push(edgeString);
			var edges_string = "["+selectedEdgesString.join(",")+"]";
			
		}	
		
		$("#tf2_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe2_prepare_cost') + edges_string +  LNG.K('aufgabe2_click_ready') +"</p>");
		
		$("#tf2_div_Frage")
            .append("<br><p> </p><p>  </p><p>  </p><center><button id=\"tf2_button_READY\">Ready!</button> </center>");
		
		$("#tf2_button_READY")
            .button()
            .click(
                function() {
					that.removeFrageTab();
					updateCost();
                    that.askQuestion1();
					that.update();
                }
            );
		 	
	}
	
	
	/**
	* Updates the potentials p_new(v) = p_old(v) - distance(s,v) for every node v in the graph 
	* @method
	*/
	function updatePotentials(){
		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
		});
		Graph.instance.nodes.forEach(function(key,node){
			ps[node.id] = node.p;
			node.p = node.p - node.state.distance;
		});
		state.current_step = STEP_PREPARECOST;
		
	}
	
	/**
	* Updates the costs for each edge with respect to the 
	* @method
	*/
	function updateCost(){

		Graph.instance.nodes.forEach(function(key,node){
			node.selectedNode = false;
			node.correct = null;
			
		});
		
		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
			if(mainLoopCounter == 1){
				edge.edges = {
					"cost": edge.resources[1],
					"cap": edge.resources[0],
					"id": edge.id
					
				};
			}
				edge.resources[1] = initialCost[edge.id] - edge.start.p + edge.end.p;
				edge.tempCost = edge.resources[1];
			
		});
		var cap = [];
		for (var i =0; i<state.edgesOfSP.length; i++){
			
			cap[i] = state.edgesOfSP[i].resources[0]-state.edgesOfSP[i].state.flow;
			
		}
		var minCap = d3.min(cap);
		var minED = Math.min(Graph.instance.nodes.get(state.sourceId).b , -Graph.instance.nodes.get(state.targetId).b);
		
		state.current_step = STEP_APPLYPATH;
		del = Math.min(minCap,minED);
	}
	

	/**
	* Calculates the maximal possible flow delta that can be augmented through the shortest path and
	* augments delta flow units along the shortest path
	* @method
	*/
	function applyPath(){
		Graph.instance.edges.forEach(function(key,edge){	
			if($.inArray(edge, selEdges) != -1){
				edge.state.flow = edge.temp;
				edge.resources[1] = edge.tempCost;

				edge.resources[0] = edge.backupCap;
			}
			edge.hin = false;
			edge.correct = null;
		});
		var cap = [];
		delta = 0;
		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
		});
		for (var i =0; i<state.edgesOfSP.length; i++){
			
			cap[i] = state.edgesOfSP[i].resources[0]-state.edgesOfSP[i].state.flow;
			
		}
        var minCap = d3.min(cap);
		
		var excessDemandMin = Math.min(Graph.instance.nodes.get(state.sourceId).b , -Graph.instance.nodes.get(state.targetId).b);
		delta = Math.min(minCap, excessDemandMin);

		for (var i = 0; i < state.edgesOfSP.length; i++)
        {
           
            var edge = state.edgesOfSP[i];

            edge.state.flow += edge.start.state.predecessor["direction"] * delta;
			minCost += delta * edge.edges["cost"];
        }
		Graph.instance.nodes.forEach(function(key,node){
			bs[node.id] = node.b;
			if(node.id == state.sourceId){
				node.b = node.b-delta;
				bOfS = node.b;
			}else if(node.id == state.targetId){
				node.b = node.b + delta;
				bOfT = node.b;
				
			}else{
				node.b = 0;
			}
		});
		
		Graph.instance.edges.forEach(function(key, edge) {
			edge.inSP = false;
			if(edge.state.flow == edge.resources[0]){
				edge.state.usedUp = true;	
			}else{
				edge.state.usedUp = false;	

			}
        });
        logger.log("Applied augmenting path with flow "+state.augmentation);
		del = 0;
		selectedEdges = [];
		state.distancesOfNodes = [];
        state.show_residual_graph = false;
		state.shortestPath = [];
        state.current_step = STEP_MAINLOOP;
		
	}
	

	this.getWarnBeforeLeave = function(){
		if(state.current_step == STEP_SELECTSOURCE || state.current_step == STEP_FINISHED){
			return false;
		}
		return true;
	}
	
	
	/**
     * Entfernt den Tab für die Frage und aktiviert den vorherigen Tab.
     * @method
     */

    this.removeFrageTab = function() {
        if($("#tf2_div_statusTabs")
            .tabs("option", "active") == 2) {
            $("#tf2_div_statusTabs")
                .tabs("option", "active", tabVorFrage);
        }
        $("#tf2_li_FrageTab")
            .remove()
            .attr("aria-controls");
        $("#tf2_div_FrageTab")
            .remove();
        $("#tf2_div_statusTabs")
            .tabs("refresh");

        frageStatus.aktiv = false;
    };
    /**
     * Entfernt den Tab für die Ergebnisse und aktiviert den vorherigen Tab.
     * @method
     */
    this.removeResultsTab = function() {
        $("#tf2_div_statusTabs")
            .tabs("option", "active", 0);
        $("#tf2_li_ErgebnisseTab")
            .remove()
            .attr("aria-controls");
        $("#tf2_div_ErgebnisseTab")
            .remove();
        $("#tf2_div_statusTabs")
            .tabs("refresh");
    };


    /**
     * Fügt einen Tab für die Frage hinzu.<br>
     * Deaktiviert außerdem die Buttons zum Weitermachen
     * @method
     */

    this.addFrageTab = function() {
        this.stopFastForward();
        ++frageStats.gestellt;
        var li = "<li id='tf2_li_FrageTab'><a href='#tf2_div_FrageTab'>" + LNG.K('aufgabe1_text_question') + " " + frageStats.gestellt + "</a></li>";
        var id = "tf2_div_FrageTab";
        $("#tf2_div_statusTabs")
            .find(".ui-tabs-nav")
            .append(li);
        $("#tf2_div_statusTabs")
            .append("<div id='" + id + "'><div id='tf2_div_Frage'></div><div id='tf2_div_Antworten'></div><div id='tf2_div_Beg'></div></div>");
        $("#tf2_div_statusTabs")
            .tabs("refresh");
        tabVorFrage = $("#tf2_div_statusTabs")
            .tabs("option", "active");
			console.log("thabVorFrage " + tabVorFrage);
        $("#tf2_div_statusTabs")
            .tabs("option", "active", 2);


        $("#tf2_button_1Schritt")
            .button("option", "disabled", true);
  
        $("#tf2_div_Frage")
            .append("<p id=\"tf2_nochNicht\"></p>");

    };
	
	/**
     * Zeigt Texte und Buttons zum Ende des Algorithmus
     * @method
     */
    this.endAlgorithm = function() {
        this.stopFastForward();
        this.showResults();
        $("#tf2_button_1Schritt")
            .button("option", "disabled", true);
        $("#tf2_button_vorspulen")
            .button("option", "disabled", true);
		
		oldGraph = randomGraph;
    };

	
	 /**
	 * Zeigt - im eigenen Tab - die Resultate der Aufgabe an.
	 * @method
	 */
    this.showResults = function() {
		
        var li = "<li id='tf2_li_ErgebnisseTab'><a href='#tf2_div_ErgebnisseTab'>" + LNG.K('aufgabe1_text_results') + "</a></li>",
            id = "tf2_div_ErgebnisseTab";
        $("#tf2_div_statusTabs")
            .find(".ui-tabs-nav")
            .append(li);
        $("#tf2_div_statusTabs")
            .append("<div id='" + id + "'></div>");
        $("#tf2_div_statusTabs")
            .tabs("refresh");
        $("#tf2_div_statusTabs")
            .tabs("option", "active", 2);
        if(frageStats.gestellt == frageStats.richtig) {
            $("#tf2_div_ErgebnisseTab")
                .append("<h2>" + LNG.K('aufgabe2_result3') + "</h2>");
            $("#tf2_div_ErgebnisseTab")
                .append("<h2>" + LNG.K('aufgabe2_result1') + "</h2>");
            $("#tf2_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe2_result2') + "</p>");
            $("#tf2_div_ErgebnisseTab")
                .append('<button id="tf2_button_Retry">' + LNG.K('aufgabe1_btn_retry') + '</button>');				
			$("#tf2_button_Retry").show();
			$("#tf2_button_Retry")
                .button()
                .click(function() {
                    that.refresh();
                });
				
        } else {
            $("#tf2_div_ErgebnisseTab")
                .append("<h2>" + LNG.K('aufgabe1_result3') + "</h2>");
            $("#tf2_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe2_result4') + " " + frageStats.gestellt/2 + "</p>");
            $("#tf2_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe2_result5') + " " + frageStats.richtig + "</p>");
            $("#tf2_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe2_result6') + " " + frageStats.falsch + "</p>");
            $("#tf2_div_ErgebnisseTab")
                .append('<button id="tf2_button_Retry">' + LNG.K('aufgabe1_btn_retry') + '</button>');
			$("#tf2_button_Retry").show();
			$("#tf2_button_Retry")
                .button()
                .click(function() {
                    that.refresh();
                });
            
        }

    };
 /**
     * Generiert eine zufällige Permutation von einem Array<br>
     * @param {Number} Anzahl von Elementen der Permutation
     * @returns {Array} zufällige Permutation
     * @method
     */
    this.generateRandomOrder = function(l) {
        var array = new Array();
        for(var i = 0; i < l; i++) array.push(i);
        for(var i = l - 1; i >= 0; i--) {
            var random = Math.floor(Math.random() * (i + 1));
            var tmp = array[i];
            array[i] = array[random];
            array[random] = tmp;
        }
        return array;

    };
	
	
	/** 
	*  Chooses a random number (that corresponds to a graph) and makes sure, that
	*  the chosen number is not the same as the last one that was chosen, i.e. the 
	*  graphs are different for any two succesive executions of exercise 1.
	*  @param {Number} Number of available graphs
    *  @returns {Number} The number of the chosen random graph
    *  @method
	*/
	
	this.chooseRandomGraph = function(numOfGraphs){
		while(randomGraph == oldGraph){
			randomGraph = Math.floor(Math.random()*(numOfGraphs)+1);
		}
			
		return randomGraph;
	}
	
	
	/** Ask for reduced costs on random edges
	*/
	this.askQuestion1 = function (){
		askquestion1 = true;
		frageStatus.aktiv = true;
        this.addFrageTab();
		$("#tf2_button_1Schritt")
            .button("option", "disabled", true);
			
        $("#tf2_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe2_question1') + "</p>");
		
		selectedEdges = selEdges;

		Graph.instance.edges.forEach(function(key,edge){
			if($.inArray(edge, selectedEdges) != -1){
				
				edge.hin = true;
				edge.rueck = false;
				edge.selected = true;

			}
			
		});
		this.update();
		$("#tf2_div_Frage")
            .append("<br><p> </p><p>  </p><p>  </p><center><button id=\"tf2_button_EV\">Check results!</button> </center>");
		  $("#tf2_button_EV")
            .button()
            .click(
                function() {
					updateCost();
                    that.handleCorrectAnswer();
                }
            );
        $("#tf2_div_Frage")
            .append("<p id=\"tf2_nochNicht\"></p>");

	}
	
	
	this.askQuestion2 = function(){
		askquestion2 = true;
		frageStatus.aktiv = true;
		
        $("#tf2_button_1Schritt")
            .button("option", "disabled", true);
		
        this.addFrageTab();
        $("#tf2_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe2_question2') + "</p>");


		selectedNodes = selNodes;
        Graph.instance.nodes.forEach(function(key,node){
			if($.inArray(node.id, selectedNodes) != -1){
				node.selected = true;
				node.selectedNode = true;
				node.addP = true;
				node.tempP = node.p;
				node.tempB = node.b;
				console.log("nodeID " + node.id + " nodeP "+ node.p );
			}
		});
		
		$("#tf2_div_Frage")
            .append("<br><p> </p><p>  </p><p>  </p><center><button id=\"tf2_button_EV\">Check results!</button> </center>");
		
		$("#tf2_button_EV")
            .button()
            .click(
                function() {
                    that.handleCorrectAnswer();
                }
            );
        $("#tf2_div_Frage")
            .append("<p id=\"tf2_nochNicht\"></p>");
        $("#tf2_div_Frage")
            .append("<p id=\"tf2_nochNicht\"></p>");
		$("#tf2_button_1Schritt")
						.button("option", "disabled", false);
		state.current_step = STEP_PREPARECOST;
	}
	
	
	
	
	
	this.handleCorrectAnswer = function() {
		$("#tf2_button_1Schritt")
            .button("option", "disabled", false);
		
		var fehler = false;
		var richtig = 0;
		if(askquestion2){
			if(geantwortet != selectedNodes.length) {
				$("#tf2_nochNicht")
					.css("color", "red");
				var fehlt = selectedNodes.length - geantwortet;
				if(fehlt == 1) {
					$("#tf2_nochNicht")
						.html("You have to fill out " + fehlt + " more field!");

				} else {
					$("#tf2_nochNicht")
						.html("You have to fill out " + fehlt + " more fields!");
				}
				
			}else{
				blurResourceEditor();
				Graph.instance.nodes.forEach(function(nodeID, d) {
					if($.inArray(d.id, selectedNodes) != -1) {
						if(d.antwortP == d.tempP) {
							
							d.correct = true;
							richtig++;
						} else {
							d.correct = false;
							fehler = true;
						}
					
						d.addP = false;
					}
				});
			
				that.update();

				$("#tf2_nochNicht")
					.html(" ");
				$("#tf2_titel")
					.html("Solution")

				$("#tf2_button_EV")
					.remove();

				var txt;
				if(fehler) {
					txt = "<p><strong>Nicht ganz richtig!</strong></p> ";
					frageStats.falsch++;
				} else {
					txt = "<p><strong>Sehr gut!</strong></p>";
					frageStats.richtig++;

				}
				$("#tf2_div_Antworten")
					.append(txt);
				$("#tf2_div_Antworten")
					.append("<p> You have filled out " + richtig + " out of " + selectedNodes.length + " fields correctly.</p>");

				$("#tf2_button_1Schritt")
					.button("option", "disabled", false);

				frageStatus = {
					"aktiv": false,
					"warAktiv": true
				};
				geantwortet = 0;
				askquestion2 = false;
				selectedNodes = [];
				selNodes = [];
			}

		}else if(askquestion1){
			
			if(geantwortet != selectedEdges.length) {
				$("#tf2_nochNicht")
					.css("color", "red");
				var fehlt = selectedEdges.length - geantwortet;
				if(fehlt == 1) {
					$("#tf2_nochNicht")
						.html("You have to fill out " + fehlt + " more field!");

				} else {
					$("#tf2_nochNicht")
						.html("You have to fill out " + fehlt + " more fields!");
				}
				
			} else {
				blurResourceEditor();

				Graph.instance.edges.forEach(function(edgeID, d) {

					if($.inArray(d, selEdges) != -1) {
						if(d.hin){
							if(d.tempCost < 0) 
								d.tempCost=0;
							if(d.tempCost == d.answerCost) {
								d.correct = true;
								richtig++;
							} else {
								d.correct = false;
								fehler = true;
							}
						}else if(d.rueck){
							if(d.tempCost < 0) 
								d.tempCost=0;

							if(-d.tempCost == answerCost[d.id]) {
								d.correct = true;
								richtig++;
							} else {
								d.correct = false;
								fehler = true;
							}
						}
					}
				});
		
				that.update();

				$("#tf2_nochNicht")
					.html(" ");
				$("#tf2_titel")
					.html("Solution")

				$("#tf2_button_EV")
					.remove();

				var txt;
				if(fehler) {
					txt = "<p><strong>Nicht ganz richtig!</strong></p> ";
					frageStats.falsch++;
				} else {
					txt = "<p><strong>Sehr gut!</strong></p>";
					frageStats.richtig++;

				}
				$("#tf2_div_Antworten")
					.append(txt);
				$("#tf2_div_Antworten")
					.append("<p> You have filled out " + richtig + " out of " + selectedEdges.length + " fields correctly.</p>");


				$("#tf2_button_1Schritt")
					.button("option", "disabled", false);
					
				
				if(Graph.instance) {
					Exercise2.prototype.update.call(this);
				}
				
				frageStatus = {
					"aktiv": false,
					"warAktiv": true
				};
				geantwortet = 0;
				askquestion1 = false;
			}
		}
		
    };

	
	this.registerEventHandlers = function() {
        var selection = d3.selectAll("g.edge");
		
        selection.on("mouseover", function(d) {
            if(d.selected) {
                svg.style("cursor", "pointer");
            }
        });
        selection.on("mouseleave", function(d) {
            if(d.selected) {
                svg.style("cursor", "default");
            }
        });
        selection.on("click", dblclickResource);
        selection.on("dblclick", dblclickResource);
		
		//for nodes
		if(frageStatus.aktiv){
			
			var selectionNodes = d3.selectAll("g.node");
			
			selectionNodes.on("mouseover", function(d) {
            if(d.selected && d.addP) {
                svg.style("cursor", "pointer");
            }
			});
			selectionNodes.on("mouseleave", function(d) {
				if(d.selected && d.addP) {
					svg.style("cursor", "default");
				}
			});
			selectionNodes.on("click", dblclickResource);
			selectionNodes.on("dblclick", dblclickResource);
		}

	
    }

    function dblclickResource(d, i, all) {
        if(d.selected && d.addP){
			d3.event.stopPropagation();
			d3.event.preventDefault();
			updateResourcesNodeP(d.resources,d);
			geantwortet++;		
        }else if(d.selected) {
            d3.event.stopPropagation();
            d3.event.preventDefault();			
			updateResources(d.resources, d);			
            geantwortet++;
		}
    }


    var myDiv = d3.select("body"); //.append("div")

    function updateResources(data, d) {

        var selection = myDiv.selectAll("input.resourceEditor")
            .data(data);
        selection.enter()
            .append("input")
            .attr("type", "number")
            .attr("id", "value")
            .attr("class", "tooltip resourceEditor")
         selection
		  .attr("value",function(a,b,c){
				d.answerCost = 0;
				d.state.flow = d.resources[0];
				d.backupCap = d.resources[0];
                d.selected = false;
                that.update();
				return 0;
		  })
		  .on("input", function(a,b,c) {
			 d.answerCost = 0;
			 
			 var val =+this.value;

			 data[1]=+this.value;
			 if(data[1]<0){
			   data[1] = 0;
			 }		
		
			
			d.answerCost = data[1];				
            d.state.cost = d.resources[1];
			d.selected = false;
			that.update()
		  })
            .style("left", function(a, b, c) {
                return(d3.event.pageX - 30 + 40 * b) + "px"
            })
            .style("top", function(a, b, c) {
                return(d3.event.pageY + 15) + "px"
            })

        selection.exit().remove();
    }

	
	 function updateResourcesNodeP(data, d) {

        var selection = myDiv.selectAll("input.resourceEditor")
            .data(data);
        selection.enter()
            .append("input")
            .attr("type", "number")
            .attr("id", "value")
            .attr("class", "tooltip resourceEditor")
         selection
		  .attr("value",function(a,b,c){
			d.antwortP = 0;
			d.selected = false;
			d.addP = false;
			that.update();
			return 0;
			
		  })
		  .on("input", function(a,b,c) {
			 data[0] = 0;
			 data[0]=+this.value;
			 
			d.antwortP = data[0];
			d.selected = false;
			d.addP = false;
			that.update()
		  })
            .style("left", function(a, b, c) {
                return(d3.event.pageX - 30 + 40 * b) + "px"
            })
            .style("top", function(a, b, c) {
                return(d3.event.pageY + 15) + "px"
            })

        selection.exit().remove();
    }
	
	
	
	
    function mousedown() {
        blurResourceEditor();
    }

    function blurResourceEditor() {
        updateResources([]);
    }

	function selectNode(){
		var keys = [];
		Graph.instance.nodes.forEach(function(nodeID, node){
			keys.push(nodeID);
			
		});
		var rand = Math.floor(Math.random()*keys.length);
		var node = Graph.instance.nodes.get(keys[rand]);
		while($.inArray(node.id,selNodes)!=-1){
			rand = Math.floor(Math.random()*keys.length);
			node = Graph.instance.nodes.get(keys[rand]);
		}
		
		
		return node.id;
	}
	
	function selectEdge() {
        //Waehle zufaellige Kante
        var keys = [];
        Graph.instance.edges.forEach(function(edgeID, edge) {
            edge.temp = edge.state.flow;
			edge.tempCost = edge.resources[1];
			if(!edge.usedUp)
				keys.push(edgeID);
        });
        var rand = Math.floor(Math.random() * keys.length);
        edge = Graph.instance.edges.get(keys[rand]);

        while($.inArray(edge,selEdges)!=-1) {
            rand = Math.floor(Math.random() * keys.length);
            edge = Graph.instance.edges.get(keys[rand]);
        }

        return edge;
    }
	
	
	this.getWarnBeforeLeave = function(){
		if(state.current_step == STEP_SELECTSOURCE || state.current_step == STEP_FINISHED){
			return false;
		}
		return true;
	}	
}

// Vererbung realisieren
Exercise2.prototype = Object.create(GraphDrawer.prototype);
Exercise2.prototype.constructor = Exercise2;
	