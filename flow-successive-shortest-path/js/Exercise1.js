/**
 * @author Gergana Kratuncheva
 * Code fuer Forschungsaufgabe 1<br>
 * Basiert auf dem Code für den normalen Algorithmus
 */
/**
 * Instanz der Forschungsaufgabe 1
 * @constructor
 * @param {BipartiteGraph} p_graph Graph, auf dem der Algorithmus ausgeführt wird
 * @param {Object} p_canvas jQuery Objekt des Canvas, in dem gezeichnet wird.
 * @param {Object} p_tab jQuery Objekt des aktuellen Tabs.
 * @augments GraphDrawer
 */
function Exercise1(svgSelection) {
    GraphDrawer.call(this, svgSelection, null, null, "tf1");

	var svgOrigin = d3.select("body")
        .select("svg");
    var svg = d3.select("#tf1_canvas_graph");
    

    //insert markers
    var definitions = svgSelection.append("defs")
        .attr("id", "line-markers");

    definitions.append("marker")
        .attr("id", "flow-arrow3")
        .attr("refX", 12) /*must be smarter way to calculate shift*/
        .attr("refY", 2)
        .attr("markerWidth", 12)
        .attr("markerHeight", 4)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M 0,0 V 4 L6,2 Z")
        .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead

    definitions.append("marker")
        .attr("id", "residual-forward3")
        .attr("refX", 14) /*must be smarter way to calculate shift*/
        .attr("refY", 3)
        .attr("markerWidth", 14)
        .attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M 2,3 L0,6 L8,3 Z")
        .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead

    definitions.append("marker")
        .attr("id", "residual-backward3")
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
     * Status der Frage.<br>
     * Keys: aktiv, warAktiv
     * Values: Boolean
     * @type Object
     */
    var frageStatus = new Object();

    /**
     * Welcher Tab (Erklärung oder Pseudocode) angezeigt wurde, bevor die Frage kam.
     * Dieser Tag wird nach der Frage wieder eingeblendet.
     * @type Boolean
     */
    var tabVorFrage = null;


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
    var debugConsole = true;
    
	var STEP_BEGINALGORITHM = 			"begin-algorithm";
    var STEP_SELECTSOURCE = 	    	"select-source";
    var STEP_SELECTTARGET =     		"select-target";
    var STEP_START =            		"start-algorithm";
	var STEP_MAINLOOP =  			    "main-loop";
	var STEP_FINDSHORTESTPATH =			"find-shortestpath";
	var STEP_UPDATEPOTENTIALS = 		"update-potentials";
	var STEP_UPDATECOST = 				"update-cost";
	var STEP_APPLYPATH =        		"apply-augmentation-path";
    var STEP_FINISHED =         		"finished";
	
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

	var count = 0;
	
	var bOfS =0;
	var bOfT =0;
	var usedUpNodes = new Array();
	var edgePrevCost = new Array();
	 /**
     * status variables
     * @type Object
     */
	 
    var state ={
      current_step: STEP_BEGINALGORITHM, //status id, //status id
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
	var mainLoopCounter = 0;
	var edges = new Array();
	
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
			if( d.p>=Number.MAX_SAFE_INTEGER-1000000){
				pAlternatives = String.fromCodePoint(8734);
			}else if(d.p<=-Number.MAX_SAFE_INTEGER+1000000 && d.p>=-Number.MAX_SAFE_INTEGER-1000000){
				pAlternatives = "-"+String.fromCodePoint(8734);
			}else{
				pAlternatives = d.p;
			}
		var res = "p: " + pAlternatives;
		return res;
	};
	

	
    this.edgeText = function(d) {
        if(!state.show_residual_graph){
			var cost;
			if( d.resources[1]>=Number.MAX_SAFE_INTEGER-1000000){
				cost = String.fromCodePoint(8734);
			}else if(d.resources[1]<=-Number.MAX_SAFE_INTEGER+1000000 && d.resources[1]>=-Number.MAX_SAFE_INTEGER-1000000){
				cost = "-"+String.fromCodePoint(8734);
			}else if(d.resources[1]<0){
				cost = 0;
			}else{
				cost = d.resources[1];
			}
	
            return "("+d.state.flow+"/"+d.resources[0]+","+cost+")";
		}else{
			var cost;
			if(d.resources[1]>=Number.MAX_SAFE_INTEGER-1000000){
				cost = String.fromCodePoint(8734);
			}else if(d.resources[1]<=-Number.MAX_SAFE_INTEGER+1000000 && d.resources[1]>=-Number.MAX_SAFE_INTEGER-1000000){
				cost = "-"+String.fromCodePoint(8734);
			}else if(d.resources[1]<0){
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

    this.edgeTextBelow =
    function(d) {
        if(state.show_residual_graph && d.state.flow > 0){
			var cost;
			if(d.resources[1]>=Number.MAX_SAFE_INTEGER-1000000){
				cost = String.fromCodePoint(8734);
			}else if(d.resources[1]<=-Number.MAX_SAFE_INTEGER+1000000 && d.resources[1]>=-Number.MAX_SAFE_INTEGER-1000000){
				cost = "-"+String.fromCodePoint(8734);
			}else if(d.resources[1]<0){
				cost = 0;
			}else{
				cost = d.resources[1];
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
                        return "url(#flow-arrow3)";
                    }
                    else
                    {
                        if(d.resources[0] - d.state.flow > 0)
                            return "url(#residual-forward3)";
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
                            return "url(#residual-backward3)";
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
        Graph.addChangeListener(function() {
            that.clear();
            that.reset();
            that.squeeze();
            that.update();
        });

        this.reset();
        this.update();
        if(Graph.instance) {
			
            Exercise1.prototype.update.call(this); //updates the graph
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
		edgesOfSP = new Array();
		distance = new Array();
		mainLoopCounter =0;
		edges = new Array();
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


    /**
     * updates status description and pseudocode highlight based on current step
     * @method
     */
     this.updateDescriptionAndPseudocode = function() {
        var sel = d3.select("#tf1_div_statusPseudocode")
            .selectAll("div");
        sel.classed("marked", function(a, pInDivCounter, divCounter) {
            return d3.select(this)
                .attr("id") === "fr-pseudocode-" + state.current_step;
        });

        var sel = d3.select("#tf1_div_statusErklaerung")
            .selectAll("div");
        sel.style("display", function(a, divCounter) {
            return(d3.select(this)
                .attr("id") === "fr-explanation-" + state.current_step) ? "block" : "none";
        });

        var disable_back_button = state.current_step === STEP_SELECTSOURCE;
        var disable_forward_button =
            (state.current_step === STEP_SELECTSOURCE ||
                state.current_step === STEP_SELECTTARGET ||
                state.current_step === STEP_FINISHED || frageStatus.aktiv);
        var disable_fastforward_button =
            (state.current_step === STEP_SELECTSOURCE ||
                state.current_step === STEP_SELECTTARGET ||
                state.current_step === STEP_FINISHED || frageStatus.aktiv);
      
        $("#tf1_button_Zurueck")
            .button("option", "disabled", disable_back_button);
        $("#tf1_button_1Schritt")
            .button("option", "disabled", disable_forward_button);
        $("#tf1_button_vorspulen")
            .button("option", "disabled", disable_fastforward_button);
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
    }
	
    this.updateVariableState = function()
    {	
		
        var sp_edge_strings = [];
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
        d3.select("#variable-value-shortestPath").text(sp_string);
		d3.select("#variable-value-delta").text(del);
		d3.select("#variable-value-distances").text(distances_string);
        d3.select("#finalflow").text(maxFlow);
        d3.select("#minCost").text(minCost);
		d3.select("#bs").text(bOfS);
		d3.select("#bt").text(bOfT);

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
				this.askQuestion1();
				getMaxFlow();			
                break;
			case STEP_MAINLOOP:
				mainLoop();
				break;
			case STEP_FINDSHORTESTPATH:
                findShortestPath();
				if(Math.random()>=0.3){
					this.askQuestion3();
				}else{
					this.askQuestion4();
				}
                break;
            case STEP_UPDATEPOTENTIALS:
                updatePotentials();
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
                //backward edges
                for (var i = 0; i < in_edges.length; i++)
                {
                    var edge_in = in_edges[i];

                    //valid residual edge (back push along incoming edge)
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



     this.calculateMinCost = function(){
       minCost = 0;
       Graph.instance.edges.forEach(
           function(key, edge)
           {
             return minCost += edge.state.flow*edge.resources[1];

           });
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
			this.endAlgorithm();
            this.stopFastForward();
            
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
			
			}else if($.inArray(temp.state.predecessor["prev_node"],state.shortestPath)!=-1 		|| temp.state.predecessor["prev_node"] == temp1.id || 
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
			Graph.instance.nodes.forEach(function(key,node){
				state.distancesOfNodes.push(node.state.distance);
			});					

		}
			answer4 = Graph.instance.nodes.get(state.targetId).p - Graph.instance.nodes.get(state.targetId).state.distance;

			state.current_step = STEP_UPDATEPOTENTIALS;	
	}


	/**
	* Updates the potentials p_new(v) = p_old(v) - distance(s,v) for every node v in the graph 
	* @method
	*/
	function updatePotentials(){

		for(var j = 1; j<state.shortestPath.length; j++){
			
			Graph.instance.edges.forEach(function(key,edge){
					if(edge.start.id == state.shortestPath[j-1] && edge.end.id == state.shortestPath[j]){
						edge.inSP = true;
						state.edgesOfSP.push(edge);
						edge.start.state.predecessor["direction"] = 1;
					}			
			});
		}
		
		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
		});
		Graph.instance.nodes.forEach(function(key,node){
			ps[node.id] = node.p;
			node.p = node.p - node.state.distance;
		});
		state.current_step = STEP_UPDATECOST;
		
	}
	
	/**
	* Updates the costs for each edge with respect to the 
	* @method
	*/
	function updateCost(){

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
			
			
		});
		var cap = [];
		for (var i =0; i<state.edgesOfSP.length; i++){
			
			cap[i] = state.edgesOfSP[i].resources[0]-state.edgesOfSP[i].state.flow;
			
		}
		var minCap = d3.min(cap);
		var minED = Math.min(Graph.instance.nodes.get(state.sourceId).b , -Graph.instance.nodes.get(state.targetId).b);
		
		state.current_step = STEP_APPLYPATH;
		del = Math.min(minCap,minED);
		that.askQuestion2();		
		
		state.current_step = STEP_APPLYPATH;		
	}
	

	/**
	* Calculates the maximal possible flow delta that can be augmented through the shortest path and
	* augments delta flow units along the shortest path
	* @method
	*/
	function applyPath(){
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
		state.distancesOfNodes = [];
        state.show_residual_graph = false;
		state.shortestPath = [];
        state.current_step = STEP_MAINLOOP;
		
	}
	
	 /**
	 * Makes the view consistent with the state
	 * @method
	 */
    this.update = function() {
		this.updateDescriptionAndPseudocode();
		this.updateVariableState();
		this.updateGraphState();

		logger.update();
		if(Graph.instance) {
			Exercise1.prototype.update.call(this); //updates the graph

		}
	}
		  
		
	/**
	 * When Tab comes into view
	 * @method
	 */
    this.activate = function() {

		$("#tf1_button_Retry").hide();
		Graph.instance.edges.forEach(function(key,edge){
			initialCost[edge.id] = edge.resources[1];
		});
		this.chooseRandomGraph(9);
        Graph.setGraph("tf1");
		Graph.loadInstance("graphs-new/Ex1/graph"+ randomGraph + ".txt");
        this.stopFastForward();
        this.clear();
        this.squeeze();
        Exercise1.prototype.update.call(this);	
		
		 $("#tf1_canvas_graph")
            .attr("visibility", "hidden");
        this.removeResultsTab();
		

        $("#tf1_button_start").show();
        $("#f1_started").hide();
        $("#tf1_button_1Schritt").button("option", "disabled", true);
        $("#tf1_button_vorspulen").button("option", "disabled", true);


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
       
        $("#tf1_button_start")
            .show();
        $("#f1-start")
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
		
		 $("#tf1_button_start")
            .click(
                function() {
                    $("#tf1_button_start").hide();
                    $("#f1-start").hide();
                    $("#f1_started").show();
					randomGraph = that.chooseRandomGraph(9);
					
					that.stopFastForward();
					that.clear();
					that.reset();
					that.update();
					that.squeeze();
					Exercise1.prototype.update.call(that);	
					
					
                   $("#tf1_button_1Schritt")
						.button("option", "disabled", false);

                    $("#tf1_canvas_graph")
                        .attr("visibility", "visible");
					Graph.instance.edges.forEach(function(key,edge){
						initialCost[edge.id] = edge.resources[1];
					});
                    state.current_step = STEP_SELECTSOURCE;
                    that.squeeze();

				});
    }

	
    /**
     * Entfernt den Tab für die Frage und aktiviert den vorherigen Tab.
     * @method
     */

    this.removeFrageTab = function() {
        if($("#tf1_div_statusTabs")
            .tabs("option", "active") == 2) {
            $("#tf1_div_statusTabs")
                .tabs("option", "active", tabVorFrage);
        }
        $("#tf1_li_FrageTab")
            .remove()
            .attr("aria-controls");
        $("#tf1_div_FrageTab")
            .remove();
        $("#tf1_div_statusTabs")
            .tabs("refresh");

        frageStatus.aktiv = false;
    };
	
	
    /**
     * Entfernt den Tab für die Ergebnisse und aktiviert den vorherigen Tab.
     * @method
     */
    this.removeResultsTab = function() {
        $("#tf1_div_statusTabs")
            .tabs("option", "active", 0);
        $("#tf1_li_ErgebnisseTab")
            .remove()
            .attr("aria-controls");
        $("#tf1_div_ErgebnisseTab")
            .remove();
        $("#tf1_div_statusTabs")
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
        var li = "<li id='tf1_li_FrageTab'><a href='#tf1_div_FrageTab'>" + LNG.K('aufgabe1_text_question') + " " + frageStats.gestellt + "</a></li>";
        var id = "tf1_div_FrageTab";
        $("#tf1_div_statusTabs")
            .find(".ui-tabs-nav")
            .append(li);
        $("#tf1_div_statusTabs")
            .append("<div id='" + id + "'><div id='tf1_div_Frage'></div><div id='tf1_div_Antworten'></div><div id='tf1_div_Beg'></div></div>");
        $("#tf1_div_statusTabs")
            .tabs("refresh");
        tabVorFrage = $("#tf1_div_statusTabs")
            .tabs("option", "active");
        $("#tf1_div_statusTabs")
            .tabs("option", "active", 2);
        $("#tf1_button_1Schritt")
            .button("option", "disabled", true);
        $("#tf1_button_vorspulen")
            .button("option", "disabled", true);
    };

	var moreFlow = false;
	
    /**
     * Stellt die Frage vom Typ 1
     * @method
     */
    this.askQuestion1 = function() {
        frageStatus.aktiv = true;
        this.addFrageTab();
        $("#tf1_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe1_question1') + "</p>");


		if(state.sourceId < state.targetId){
			this.frageParam = {
				Antwort: LNG.K('aufgabe1_answer1'),
				AntwortGrund: "<p>" + LNG.K('aufgabe1_answer1_reason1') + "</p>",
				gewusst: true
			};
			moreFlow = true;
		}else{
			this.frageParam = {
				Antwort: LNG.K('aufgabe1_answer1_2'),
				AntwortGrund: "<p>" + LNG.K('aufgabe1_answer1_reason2') + "</p>",
				gewusst: true
			};
			moreFlow = false;
	
		}

        // Reihenfolge zufaellig angezeigt
        var antwortReihenfolge = this.generateRandomOrder(2);
		
		if(state.sourceId < state.targetId){
			var Antworten = [LNG.K('aufgabe1_text_yes'), LNG.K('aufgabe1_text_no')];
		}else{
	        var Antworten = [LNG.K('aufgabe1_text_no'), LNG.K('aufgabe1_text_yes')];
		}
        for(var i = 0; i < antwortReihenfolge.length; i++) {
            $("#tf1_div_Antworten")
                .append("<input type=\"radio\" id=\"tf1_input_frage1_" + antwortReihenfolge[i].toString() + "\" name=\"frage1\"/>" + "<label id=\"tf1_label_frage1_" + antwortReihenfolge[i].toString() + "\" for=\"tf1_input_frage1_" + antwortReihenfolge[i].toString() + "\">" + Antworten[antwortReihenfolge[i]] + "</label><br>");

        }
        $("#tf1_div_Antworten")
            .append("<br>");
		
        $("#tf1_input_frage2")
            .click(function() {
                $("#tf1_label_frage2")
                    .addClass("ui-state-error");
                document.getElementById("tf1_input_frage1_1")
                    .disabled = true;
                document.getElementById("tf1_input_frage1_0")
                    .disabled = true;
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });


        $("#tf1_input_frage1_0")
            .click(function() {
                document.getElementById("tf1_input_frage1_1")
                    .disabled = true;
                document.getElementById("tf1_input_frage1_0")
                    .disabled = true;
                that.frageParam.gewusst = true;
                that.handleCorrectAnswer();
            });

					
				
    };
	
	
	
	this.askQuestion2 = function(){
		frageStatus.aktiv = true;
        this.addFrageTab();
        $("#tf1_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe1_question2') + "</p>");

		var richtigeAntwort = Graph.instance.nodes.get(state.sourceId).b - del;

		var randomAntwort0=0;
		if(richtigeAntwort != 0){
			randomAntwort0 = 0;
		}else{
			while(randomAntwort0 == 0){
				randomAntwort0 = Math.floor(Math.random()*11 + Math.random()*13 + Math.random()*maxFlow) % (maxFlow - 1);
			}
		}
		
		var randomAntwort1 = Math.floor(Math.random()*(richtigeAntwort + 9));
		
		while(randomAntwort1 == richtigeAntwort || randomAntwort1==randomAntwort0 || randomAntwort1 == currentFlow){
			randomAntwort1 = Math.floor(Math.random()*(richtigeAntwort + 9));
		}
		
		var randomAntwort2 = Math.floor(Math.random()*(richtigeAntwort + 13));

		while(randomAntwort2 == richtigeAntwort || randomAntwort2 == currentFlow || randomAntwort2 == randomAntwort0 || randomAntwort2 == randomAntwort1){
			randomAntwort2 = Math.floor(Math.random()*(richtigeAntwort + 13));
		}
		
		var randomAntwort3 = Math.floor(Math.random()*(richtigeAntwort + 5));
		
		while(randomAntwort3 == richtigeAntwort || randomAntwort3 == currentFlow || randomAntwort3 == randomAntwort0 || randomAntwort3 == randomAntwort1 || randomAntwort3 == randomAntwort2){
			randomAntwort3 = Math.floor(Math.random()*(richtigeAntwort + 5));
		}
		var randomAntwort4 = Math.floor(Math.random()*(richtigeAntwort + 7));
		
		while(randomAntwort4 == richtigeAntwort || randomAntwort4 == currentFlow || randomAntwort4 == randomAntwort0 || randomAntwort4 == randomAntwort1 || randomAntwort4 == randomAntwort2 || randomAntwort4 == randomAntwort3){
			randomAntwort4 = Math.floor(Math.random()*(richtigeAntwort +7));
		}		
		
		 var antwortReihenfolge = this.generateRandomOrder(6);
        var Antworten = [richtigeAntwort, randomAntwort0, randomAntwort1, randomAntwort2, randomAntwort3 , randomAntwort4];

        for(var i = 0; i < antwortReihenfolge.length; i++) {
            $("#tf1_div_Antworten")
                .append("<input type=\"radio\" id=\"tf1_input_frage2_" + antwortReihenfolge[i].toString() + "\" name=\"frage2\"/>" + "<label id=\"tf1_label_frage2_" + antwortReihenfolge[i].toString() + "\" for=\"tf1_input_frage2_" + antwortReihenfolge[i].toString() + "\">" + Antworten[antwortReihenfolge[i]] + "</label><br>");

        }
        $("#tf1_div_Antworten")
            .append("<br>");

        for(var i = 0; i < 5; i++) {
            $("#tf1_input_frage2_" + i)
                .click(function() {
                    document.getElementById("tf1_input_frage2_0")
                        .disabled = true;
                    document.getElementById("tf1_input_frage2_1")
                        .disabled = true;
                    document.getElementById("tf1_input_frage2_2")
                        .disabled = true;
                    document.getElementById("tf1_input_frage2_3")
                        .disabled = true;
                    document.getElementById("tf1_input_frage2_4")
                        .disabled = true;
                    document.getElementById("tf1_input_frage2_5")
                        .disabled = true;
                    
                });
        }


        $("#tf1_input_frage2_0")
            .click(function() {
                that.frageParam.gewusst = true;
                that.handleCorrectAnswer();
            });
        $("#tf1_input_frage2_1")
            .click(function() {
                $("#tf1_label_frage2_1")
                    .addClass("ui-state-error");
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });
        $("#tf1_input_frage2_2")
            .click(function() {
                $("#tf1_label_frage2_2")
                    .addClass("ui-state-error");
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });
        $("#tf1_input_frage2_3")
            .click(function() {
                $("#tf1_label_frage2_3")
                    .addClass("ui-state-error");
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });
        $("#tf1_input_frage2_4")
            .click(function() {
                $("#tf1_label_frage2_4")
                    .addClass("ui-state-error");
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });
        $("#tf1_input_frage2_5")
            .click(function() {
                $("#tf1_label_frage2_5")
                    .addClass("ui-state-error");
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });


        this.frageParam = {
            Antwort: richtigeAntwort,
            AntwortGrund: "<p>" + LNG.K('answer_aufgabe2_reason') +
                richtigeAntwort +
                ".</p>",
            gewusst: true
        };
		
	}
	
	
    /**
     * Zeigt Texte und Buttons zum Ende des Algorithmus
     * @method
     */
    this.endAlgorithm = function() {
        this.stopFastForward();
        this.showResults();
        $("#tf1_button_1Schritt")
            .button("option", "disabled", true);
        $("#tf1_button_vorspulen")
            .button("option", "disabled", true);
		
		oldGraph = randomGraph;
    };


	
	
	
	 /**
	 * Zeigt - im eigenen Tab - die Resultate der Aufgabe an.
	 * @method
	 */
    this.showResults = function() {

        var li = "<li id='tf1_li_ErgebnisseTab'><a href='#tf1_div_ErgebnisseTab'>" + LNG.K('aufgabe1_text_results') + "</a></li>",
            id = "tf1_div_ErgebnisseTab";
        $("#tf1_div_statusTabs")
            .find(".ui-tabs-nav")
            .append(li);
        $("#tf1_div_statusTabs")
            .append("<div id='" + id + "'></div>");
        $("#tf1_div_statusTabs")
            .tabs("refresh");
        $("#tf1_div_statusTabs")
            .tabs("option", "active", 2);
        if(frageStats.gestellt == frageStats.richtig) {
            $("#tf1_div_ErgebnisseTab")
                .append("<h2>" + LNG.K('aufgabe1_result3') + "</h2>");
            $("#tf1_div_ErgebnisseTab")
                .append("<h2>" + LNG.K('aufgabe1_result1') + "</h2>");
            $("#tf1_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe1_result2') + "</p>");
            $("#tf1_div_ErgebnisseTab")
                .append('<button id="tf1_button_Retry">' + LNG.K('aufgabe1_btn_retry') + '</button>');				
			$("#tf1_button_Retry").show();
			$("#tf1_button_Retry")
                .button()
                .click(function() {
                    that.refresh();
                });
				
        } else {
            $("#tf1_div_ErgebnisseTab")
                .append("<h2>" + LNG.K('aufgabe1_result3') + "</h2>");
            $("#tf1_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe1_result4') + " " + frageStats.gestellt + "</p>");
            $("#tf1_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe1_result5') + " " + frageStats.richtig + "</p>");
            $("#tf1_div_ErgebnisseTab")
                .append("<p>" + LNG.K('aufgabe1_result6') + " " + frageStats.falsch + "</p>");
            $("#tf1_div_ErgebnisseTab")
                .append('<button id="tf1_button_Retry">' + LNG.K('aufgabe1_btn_retry') + '</button>');
			$("#tf1_button_Retry").show();
			$("#tf1_button_Retry")
                .button()
                .click(function() {
                    that.refresh();
                });
            
        }

    };

	

    /**
     * Stellt die Frage vom Typ 3
     * @method
     */
    this.askQuestion3 = function() {
		count++;
		var sp_node_strings = [];
        for(var i = 0; i<state.shortestPath.length; i++){
			if($.inArray(state.shortestPath[i],state.shortestPath.slice(0,i))!=-1){
				continue;
			}
            var edge_string = "";
            if(state.shortestPath[i] == state.sourceId)
                edge_string+= "s";
            else if(state.shortestPath[i] == state.targetId)
                edge_string += "t";
            else
                edge_string += state.shortestPath[i];

            sp_node_strings.push(edge_string);
        }
        var sp_string = sp_node_strings.join(",");

        frageStatus.aktiv = true;
        this.addFrageTab();
        $("#tf1_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe1_question3') + "</p>");
        

		var answer = "("+sp_string+")";
		
        this.frageParam = {
            Antwort: answer,
            AntwortGrund: "<p>" + LNG.K('aufgabe1_answer3_reason1') + "d"
                	+ answer 
                + "</p>",
            gewusst: true
        };

		
		if(randomGraph == 1 || randomGraph == 5 || count > 1){
			
			 // Reihenfolge zufaellig angezeigt
			var antwortReihenfolge = this.generateRandomOrder(3);
		
			var path = findPath();
			while(beautifyPath(path).localeCompare(sp_node_strings)==0){
				path = findPath();
			}
			var randomAnswer = "("+beautifyPath(path)+")";
			
			var path1 = findPath();
			while(beautifyPath(path1).localeCompare(sp_node_strings)==0 || beautifyPath(path1).localeCompare(beautifyPath(path))==0){
				path1 = findPath();
			}
			var randomAnswer1 = "("+ beautifyPath(path1)+")";
			
			//Anworten array: korrekte Loesung immer an erster stelle
			var Antworten = [answer,randomAnswer,randomAnswer1];

			for(var i = 0; i < antwortReihenfolge.length; i++) {
				$("#tf1_div_Antworten")
					.append("<input type=\"radio\" id=\"tf1_input_frage3_" + antwortReihenfolge[i].toString() + "\" name=\"frage1\"/>" + "<label id=\"tf1_label_frage1_" + antwortReihenfolge[i].toString() + "\" for=\"tf1_input_frage3_" + antwortReihenfolge[i].toString() + "\">" + Antworten[antwortReihenfolge[i]] + "</label><br>");

			}
			$("#tf1_div_Antworten")
            .append("<br>");

			$("#tf1_input_frage3_1")
            .click(function() {

                $("#tf1_label_frage3_1")
                    .addClass("ui-state-error");
				document.getElementById("tf1_input_frage3_2")
                    .disabled = true;
                document.getElementById("tf1_input_frage3_1")
                    .disabled = true;
                document.getElementById("tf1_input_frage3_0")
                    .disabled = true;
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });

			$("#tf1_input_frage3_2")
            .click(function() {

                $("#tf1_label_frage3_2")
                    .addClass("ui-state-error");
				document.getElementById("tf1_input_frage3_2")
                    .disabled = true;
                document.getElementById("tf1_input_frage3_1")
                    .disabled = true;
                document.getElementById("tf1_input_frage3_0")
                    .disabled = true;
                that.frageParam.gewusst = false;
                that.handleCorrectAnswer();
            });

			$("#tf1_input_frage3_0")
            .click(function() {
				document.getElementById("tf1_input_frage3_2")
                    .disabled = true;
                document.getElementById("tf1_input_frage3_1")
                    .disabled = true;
                document.getElementById("tf1_input_frage3_0")
                    .disabled = true;
                that.frageParam.gewusst = true;
                that.handleCorrectAnswer();
            });

		}else{
						
			 // Reihenfolge zufaellig angezeigt
			var antwortReihenfolge = this.generateRandomOrder(4);
			
			var path = findPath();
			while(beautifyPath(path).localeCompare(sp_node_strings)==0){
				path = findPath();
			}
			var randomAnswer = "("+beautifyPath(path)+")";
						
			var path1 = findPath();
			while(beautifyPath(path1).localeCompare(sp_node_strings)==0 || beautifyPath(path1).localeCompare(beautifyPath(path))==0){
				path1 = findPath();
			}
			var randomAnswer1 = "("+ beautifyPath(path1)+")";
				
			
			var path2 = findPath();
			while(beautifyPath(path2).localeCompare(sp_node_strings)==0|| beautifyPath(path2).localeCompare(beautifyPath(path))==0 || beautifyPath(path2).localeCompare(beautifyPath(path1))==0){
				path2 = findPath();
			}
			var randomAnswer2 = "(" + beautifyPath(path2) + ")";

			//Anworten array: korrekte Loesung immer an erster stelle
			var Antworten = [answer,randomAnswer,randomAnswer1,randomAnswer2];

			for(var i = 0; i < antwortReihenfolge.length; i++) {
				$("#tf1_div_Antworten")
					.append("<input type=\"radio\" id=\"tf1_input_frage3_" + antwortReihenfolge[i].toString() + "\" name=\"frage1\"/>" + "<label id=\"tf1_label_frage1_" + antwortReihenfolge[i].toString() + "\" for=\"tf1_input_frage3_" + antwortReihenfolge[i].toString() + "\">" + Antworten[antwortReihenfolge[i]] + "</label><br>");

			}
			$("#tf1_div_Antworten")
            .append("<br>");

			for(var i = 1; i<=3; i++){
				
				$("#tf1_input_frage3_" + i)
				.click(function() {

					$("#tf1_label_frage3_" + i)
						.addClass("ui-state-error");
					document.getElementById("tf1_input_frage3_3")
						.disabled = true;
					document.getElementById("tf1_input_frage3_2")
						.disabled = true;
					document.getElementById("tf1_input_frage3_1")
						.disabled = true;
					document.getElementById("tf1_input_frage3_0")
						.disabled = true;
					that.frageParam.gewusst = false;
					that.handleCorrectAnswer();
				});
			}
			
			$("#tf1_input_frage3_0")
				.click(function() {
					document.getElementById("tf1_input_frage3_3")
						.disabled = true;
					document.getElementById("tf1_input_frage3_2")
						.disabled = true;
					document.getElementById("tf1_input_frage3_1")
						.disabled = true;
					document.getElementById("tf1_input_frage3_0")
						.disabled = true;
					that.frageParam.gewusst = true;
					that.handleCorrectAnswer();
				});
			
		}
        


    };
	
	
	function findPath(){
		var graph = Graph.instance;
		var node = graph.nodes.get(state.sourceId);
		var path = [];
		path.push(node.id);
		while(node.id != state.targetId){
			var outEdges = node.getOutEdges();
			var outEdgesMixed = mixArray(outEdges);
			while($.inArray(outEdgesMixed[0].end.id, path) != -1){
				outEdgesMixed = mixArray(outEdges);
			}
			node = graph.nodes.get(outEdgesMixed[0].end.id);
			path.push(node.id);
			
		}
		return path;
		
	}
	
	
	function mixArray(arr) {
        var tmp, rand;
        for(var i = 0; i < arr.length; i++) {
            rand = Math.floor(Math.random() * arr.length);
            tmp = arr[i];
            arr[i] = arr[rand];
            arr[rand] = tmp;
        }
        return arr;
    }
	
	function beautifyPath(path){
		var path_node_strings = [];
		for(var i = 0; i<path.length; i++){
			if($.inArray(path[i],path.slice(0,i))!=-1){
				continue;
			}
            var edge_string = "";
            if(path[i] == state.sourceId)
                edge_string+= "s";
            else if(path[i] == state.targetId)
                edge_string += "t";
            else
                edge_string += path[i];

         

            path_node_strings.push(edge_string);
        }
        var path_string = path_node_strings.join(",");
		return path_string;
		
	}

    this.askQuestion4 = function() {


        frageStatus.aktiv = true;
        this.addFrageTab();
        $("#tf1_div_Frage")
            .append("<p class=\"frage\">" + LNG.K('aufgabe1_question4') + "</p>");


        this.frageParam = {
            Antwort: answer4,
            AntwortGrund: "<p>" + LNG.K('aufgabe1_answer4_reason1')
                + answer4
                + "</p>",
            gewusst: true
        };

		var randomAnswer = Math.floor(Math.random()*(answer4+2));
		while(randomAnswer == answer4){
			randomAnswer =  Math.floor(Math.random()*(answer4+2));
			
		}
		
		var randomAnswer1 =  Math.floor(Math.random()*(answer4-2));
		while(randomAnswer1 == answer4||randomAnswer1==randomAnswer){
			randomAnswer1 =  Math.floor(Math.random()*(answer4-2));
			
		}
		
		var randomAnswer2 =  answer4+1;
		while(randomAnswer2 == answer4||randomAnswer2==randomAnswer||randomAnswer2==randomAnswer1){
			randomAnswer2++;
			
		}
		
		var randomAnswer3 =  answer4-1;
		while(randomAnswer3 == answer4||randomAnswer3==randomAnswer||randomAnswer3==randomAnswer1||randomAnswer3==randomAnswer2){
			randomAnswer3--;
			
		}
				
        // Reihenfolge zufaellig angezeigt
        var antwortReihenfolge = this.generateRandomOrder(5);
        //Anworten array: korrekte Loesung immer an erster stelle

        var Antworten = [answer4, randomAnswer, randomAnswer1, randomAnswer2, randomAnswer3];

        for(var i = 0; i < antwortReihenfolge.length; i++) {
            $("#tf1_div_Antworten")
                .append("<input type=\"radio\" id=\"tf1_input_frage4_" + antwortReihenfolge[i].toString() + "\" name=\"frage1\"/>" + "<label id=\"tf1_label_frage1_" + antwortReihenfolge[i].toString() + "\" for=\"tf1_input_frage4_" + antwortReihenfolge[i].toString() + "\">" + Antworten[antwortReihenfolge[i]] + "</label><br>");

        }
        $("#tf1_div_Antworten")
            .append("<br>");

		for(var i = 1; i<=4;i++){
			$("#tf1_input_frage4_" + i)
				.click(function() {
					$("#tf1_label_frage4_" + i)
						.addClass("ui-state-error");
					document.getElementById("tf1_input_frage4_4")
						.disabled = true;
					document.getElementById("tf1_input_frage4_3")
						.disabled = true;
					document.getElementById("tf1_input_frage4_2")
						.disabled = true;
					document.getElementById("tf1_input_frage4_1")
						.disabled = true;
					document.getElementById("tf1_input_frage4_0")
						.disabled = true;
					that.frageParam.gewusst = false;
					that.handleCorrectAnswer();
				});
		}

        $("#tf1_input_frage4_0")
            .click(function() {
				document.getElementById("tf1_input_frage4_4")
                    .disabled = true;
				document.getElementById("tf1_input_frage4_3")
                    .disabled = true;
				document.getElementById("tf1_input_frage4_2")
                    .disabled = true;
                document.getElementById("tf1_input_frage4_1")
                    .disabled = true;
                document.getElementById("tf1_input_frage4_0")
                    .disabled = true;
                that.frageParam.gewusst = true;
                that.handleCorrectAnswer();
            });



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

	
	this.handleCorrectAnswer = function() {
        $("#tf1_button_1Schritt")
            .button("option", "disabled", false);
        $("#tf1_button_vorspulen")
            .button("option", "disabled", false);


        if(this.frageParam.gewusst) {
            $("p.frage")
                .css("color", const_Colors.GreenText);
            $("#tf1_div_Antworten")
                .html("<h2>" + LNG.K('aufgabe1_text_right_answer') + " " + this.frageParam.Antwort + "</h2>");
            $("#tf1_div_Beg")
                .append(this.frageParam.AntwortGrund);
            frageStats.richtig++;
        } else {
            $("p.frage")
                .css("color", const_Colors.RedText);
            $("#tf1_div_Beg")
                .html("<h2>" + LNG.K('aufgabe1_text_wrong_answer') + "</h2>");
            $("#tf1_div_Antworten")
                .html("<h2>" + LNG.K('aufgabe1_text_right_answer') + " " + this.frageParam.Antwort + "</h2>");
            $("#tf1_div_Beg")
                .append(this.frageParam.AntwortGrund);
            frageStats.falsch++;
        }
        // update graph
        if(Graph.instance) {
            Exercise1.prototype.update.call(this);
        }
        frageStatus = {
            "aktiv": false,
            "warAktiv": true
        };

    };

	this.getWarnBeforeLeave = function(){
		if(state.current_step == STEP_SELECTSOURCE || state.current_step == STEP_FINISHED){
			return false;
		}
		return true;
	}	
}

// Vererbung realisieren
Exercise1.prototype = Object.create(GraphDrawer.prototype);
Exercise1.prototype.constructor = Exercise1;