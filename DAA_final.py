import tkinter as tk
from tkinter import ttk, messagebox
import customtkinter as ctk
import webbrowser
import folium
import random
import threading
import time
from datetime import datetime, timedelta
from deep_translator import GoogleTranslator
import speech_recognition as sr
import tempfile
import os
import hashlib
import math
import json
from collections import defaultdict, deque
import heapq
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

# Enhanced data structures for better performance
@dataclass
class Place:
    name: str
    coords: Tuple[float, float]
    cost: int
    rating: float
    description: str
    visit_time: float
    category: str
    popularity_score: float = 0.0

@dataclass
class Route:
    path: List[str]
    distance: float
    time: float
    cost: int

# Binary Search Tree for efficient place searching
class PlaceBST:
    def __init__(self):
        self.root = None
    
    class Node:
        def __init__(self, place: Place):
            self.place = place
            self.left = None
            self.right = None
    
    def insert(self, place: Place):
        if not self.root:
            self.root = self.Node(place)
        else:
            self._insert_recursive(self.root, place)
    
    def _insert_recursive(self, node, place):
        if place.rating < node.place.rating:
            if node.left is None:
                node.left = self.Node(place)
            else:
                self._insert_recursive(node.left, place)
        else:
            if node.right is None:
                node.right = self.Node(place)
            else:
                self._insert_recursive(node.right, place)
    
    def search_by_rating_range(self, min_rating: float, max_rating: float) -> List[Place]:
        result = []
        self._search_range_recursive(self.root, min_rating, max_rating, result)
        return result
    
    def _search_range_recursive(self, node, min_rating, max_rating, result):
        if not node:
            return
        
        if min_rating <= node.place.rating <= max_rating:
            result.append(node.place)
        
        if node.place.rating > min_rating:
            self._search_range_recursive(node.left, min_rating, max_rating, result)
        if node.place.rating < max_rating:
            self._search_range_recursive(node.right, min_rating, max_rating, result)

# Places data
places_data = {
    "Clock Tower": Place("Clock Tower", (30.3256, 78.0437), 0, 4.2, "Historic landmark in city center", 1.0, "Landmark", 0.9),
    "Robber's Cave": Place("Robber's Cave", (30.3956, 78.0805), 20, 4.5, "Natural cave formation with stream", 2.5, "Adventure", 0.8),
    "Sahastradhara": Place("Sahastradhara", (30.3872, 78.1316), 30, 4.3, "Beautiful waterfalls with sulfur springs", 2.0, "Nature", 0.7),
    "Forest Research Institute": Place("Forest Research Institute", (30.3544, 77.9995), 25, 4.7, "Colonial-era research institute with museum", 2.0, "Cultural", 0.6),
    "Tapkeshwar Temple": Place("Tapkeshwar Temple", (30.3086, 78.0211), 10, 4.1, "Ancient cave temple dedicated to Lord Shiva", 1.5, "Religious", 0.8),
    "Indian Military Academy": Place("Indian Military Academy", (30.3417, 77.9913), 100, 5.0, "Prestigious military training academy", 2.5, "Institution", 0.5),
    "Mindrolling Monastery": Place("Mindrolling Monastery", (30.3131, 77.9814), 0, 4.6, "Beautiful Tibetan Buddhist monastery", 1.5, "Religious", 0.7),
    "Paltan Bazaar": Place("Paltan Bazaar", (30.3241, 78.0402), 0, 4.0, "Vibrant local market for shopping", 2.0, "Market", 0.95),
    "Maldevta": Place("Maldevta", (30.3745, 78.1234), 50, 4.4, "Scenic spot for trekking and rafting", 3.0, "Adventure", 0.75),
    "Buddha Temple": Place("Buddha Temple", (30.3023, 77.9865), 0, 4.5, "Peaceful Tibetan temple with gardens", 1.5, "Religious", 0.7),
    "Lacchwala": Place("Lacchiwala", (30.2536, 78.1087), 40, 4.2, "Picnic spot with water activities", 2.5, "Adventure", 0.65),
    "Rajaji National Park": Place("Rajaji National Park", (30.2678, 78.1602), 150, 4.6, "Wildlife sanctuary with jeep safaris", 4.0, "Nature", 0.8)
}

# Simplified graph 
graph = {
    "Clock Tower": {"Robber's Cave": {"dist": 5, "time": 15}, "Forest Research Institute": {"dist": 3, "time": 10}, "Tapkeshwar Temple": {"dist": 3, "time": 10}, "Paltan Bazaar": {"dist": 1, "time": 5}},
    "Robber's Cave": {"Sahastradhara": {"dist": 4, "time": 12}, "Maldevta": {"dist": 6, "time": 18}},
    "Sahastradhara": {"Forest Research Institute": {"dist": 6, "time": 18}, "Maldevta": {"dist": 5, "time": 15}},
    "Forest Research Institute": {"Tapkeshwar Temple": {"dist": 2, "time": 8}, "Indian Military Academy": {"dist": 1, "time": 5}},
    "Tapkeshwar Temple": {"Clock Tower": {"dist": 3, "time": 10}, "Mindrolling Monastery": {"dist": 4, "time": 12}, "Buddha Temple": {"dist": 3, "time": 10}},
    "Indian Military Academy": {"Forest Research Institute": {"dist": 1, "time": 5}},
    "Mindrolling Monastery": {"Tapkeshwar Temple": {"dist": 4, "time": 12}, "Buddha Temple": {"dist": 2, "time": 8}},
    "Paltan Bazaar": {"Clock Tower": {"dist": 1, "time": 5}, "Buddha Temple": {"dist": 4, "time": 12}},
    "Maldevta": {"Robber's Cave": {"dist": 6, "time": 18}, "Sahastradhara": {"dist": 5, "time": 15}, "Lacchiwala": {"dist": 7, "time": 20}},
    "Buddha Temple": {"Mindrolling Monastery": {"dist": 2, "time": 8}, "Tapkeshwar Temple": {"dist": 3, "time": 10}, "Paltan Bazaar": {"dist": 4, "time": 12}},
    "Lacchiwala": {"Maldevta": {"dist": 7, "time": 20}, "Rajaji National Park": {"dist": 8, "time": 25}},
    "Rajaji National Park": {"Lacchiwala": {"dist": 8, "time": 25}}
}

class SimplifiedTravelGuideApp:
    def __init__(self, root):
        # Theme setup
        self.current_theme = "dark"
        ctk.set_appearance_mode(self.current_theme)
        ctk.set_default_color_theme("blue")
        
        self.root = root
        self.root.title("🌟 Interactive Travel and Tourism Guide")
        self.root.geometry("1400x900")
        self.root.minsize(1200, 800)
        
        # Initialize data structures
        self.place_bst = PlaceBST()
        self.route_cache = {}
        self.weather_cache = {}
        self.recognizer = sr.Recognizer()
        
        # Populate BST
        for place in places_data.values():
            self.place_bst.insert(place)
        
        # Animation variables
        self.animation_running = False
        
        self._setup_ui()
        self._start_background_updates()

    def _setup_ui(self):
        # Main container
        self.main_container = ctk.CTkFrame(self.root, corner_radius=0)
        self.main_container.pack(fill="both", expand=True)
        
        # Header with theme toggle
        self._create_enhanced_header()
        
        # Main content area
        self.content_frame = ctk.CTkFrame(self.main_container)
        self.content_frame.pack(fill="both", expand=True, padx=10, pady=5)
        
        # Sidebar with enhanced navigation
        self._create_enhanced_sidebar()
        
        # Tabbed interface
        self._create_enhanced_tabs()

    def _create_enhanced_header(self):
        header = ctk.CTkFrame(self.main_container, height=100, corner_radius=15)
        header.pack(fill="x", padx=10, pady=10)
        header.pack_propagate(False)
        
        # Title
        title_frame = ctk.CTkFrame(header, fg_color="transparent")
        title_frame.pack(side="left", fill="both", expand=True)
        
        main_title = ctk.CTkLabel(
            title_frame,
            text="🌟 Interactive Travel and Tourism guide",
            font=ctk.CTkFont(family="Helvetica", size=28, weight="bold")
        )
        main_title.pack(pady=10)
        
        subtitle = ctk.CTkLabel(
            title_frame,
            text="Discover Dehradun with your travel buddy",
            font=ctk.CTkFont(size=14),
            text_color=("gray60", "gray40")
        )
        subtitle.pack()
        
        # Control panel
        controls = ctk.CTkFrame(header, width=300)
        controls.pack(side="right", fill="y", padx=10, pady=10)
        controls.pack_propagate(False)
        
        # Theme toggle
        theme_frame = ctk.CTkFrame(controls, fg_color="transparent")
        theme_frame.pack(pady=5)
        
        ctk.CTkLabel(theme_frame, text="🎨 Theme:", font=ctk.CTkFont(size=12)).pack(side="left", padx=5)
        self.theme_switch = ctk.CTkSwitch(
            theme_frame,
            text="Dark/Light",
            command=self._toggle_theme,
            font=ctk.CTkFont(size=10)
        )
        self.theme_switch.pack(side="left", padx=5)
        
        # Real-time clock
        self.clock_label = ctk.CTkLabel(
            controls,
            text="",
            font=ctk.CTkFont(size=12, weight="bold")
        )
        self.clock_label.pack(pady=5)
        self._update_clock()

    def _create_enhanced_sidebar(self):
        sidebar_frame = ctk.CTkFrame(self.content_frame, width=250, corner_radius=15)
        sidebar_frame.pack(side="left", fill="y", padx=5, pady=5)
        sidebar_frame.pack_propagate(False)
        
        # Sidebar header
        sidebar_header = ctk.CTkLabel(
            sidebar_frame,
            text="🧭 Navigation",
            font=ctk.CTkFont(size=18, weight="bold")
        )
        sidebar_header.pack(pady=15)
        
        # Navigation buttons (removed analytics)
        self.nav_buttons = {}
        tabs_config = [
            ("🏠", "Dashboard", "dashboard"),
            ("🧳", "Smart Planner", "planner"),
            ("🌤", "Weather", "weather"),
            ("🅿", "Parking ", "parking"),
            ("🗣", "Translator", "translator"),
            ("🧭", "Route Optimizer", "route"),
            ("📍", "Interactive Map", "map")
        ]
        
        for icon, text, tab_id in tabs_config:
            btn = ctk.CTkButton(
                sidebar_frame,
                text=f"{icon} {text}",
                command=lambda t=tab_id: self._switch_tab_animated(t),
                height=45,
                corner_radius=10,
                font=ctk.CTkFont(size=14, weight="bold"),
                hover_color=("gray70", "gray30")
            )
            btn.pack(pady=8, padx=15, fill="x")
            self.nav_buttons[tab_id] = btn

    def _create_enhanced_tabs(self):
        # Main content area
        self.tab_container = ctk.CTkFrame(self.content_frame, corner_radius=15)
        self.tab_container.pack(side="right", fill="both", expand=True, padx=5, pady=5)
        
        # Create all tab frames
        self.tabs = {}
        self._create_dashboard_tab()
        self._create_smart_planner_tab()
        self._create_weather_pro_tab()
        self._create_parking_ai_tab()
        self._create_voice_translator_tab()
        self._create_route_optimizer_tab()
        self._create_interactive_map_tab()
        
        # Show dashboard by default
        self._switch_tab_animated("dashboard")

    def _create_dashboard_tab(self):
        frame = ctk.CTkScrollableFrame(self.tab_container, corner_radius=10)
        self.tabs["dashboard"] = frame
        
        # Welcome section
        welcome_frame = ctk.CTkFrame(frame, height=150, corner_radius=15)
        welcome_frame.pack(fill="x", padx=10, pady=10)
        welcome_frame.pack_propagate(False)
        
        welcome_title = ctk.CTkLabel(
            welcome_frame,
            text="🎯 Welcome to Dehradun",
            font=ctk.CTkFont(size=24, weight="bold")
        )
        welcome_title.pack(pady=20)
        
        welcome_desc = ctk.CTkLabel(
            welcome_frame,
            text="Enjoy your trip like never before with smart recommendations,\nreal-time updates, and intelligent route optimization.",
            font=ctk.CTkFont(size=14),
            text_color=("gray60", "gray40")
        )
        welcome_desc.pack(pady=10)
        
        # Feature cards (removed analytics)
        features_frame = ctk.CTkFrame(frame, fg_color="transparent")
        features_frame.pack(fill="x", padx=10, pady=10)
        
        self._create_feature_cards(features_frame)

    def _create_feature_cards(self, parent):
        cards_data = [
            ("🤖", "Smart Recommendations", "Smart suggestions based on your preferences", "planner"),
            ("⚡", "Real-time Updates", "Live weather, traffic, and parking data", "weather"),
            ("🎯", "Route Optimization", "Find the best paths with A* algorithm", "route"),
            ("🗣", "Voice Translation", "Communicate in multiple languages", "translator")
        ]
        
        # Create grid layout
        for i, (icon, title, desc, tab) in enumerate(cards_data):
            row = i // 2
            col = i % 2
            
            card = ctk.CTkFrame(parent, height=120, corner_radius=12)
            card.grid(row=row, column=col, padx=10, pady=10, sticky="ew")
            
            # Configure grid weights
            parent.grid_columnconfigure(col, weight=1)
            
            # Card content
            icon_label = ctk.CTkLabel(card, text=icon, font=ctk.CTkFont(size=30))
            icon_label.pack(pady=10)
            
            title_label = ctk.CTkLabel(card, text=title, font=ctk.CTkFont(size=16, weight="bold"))
            title_label.pack()
            
            desc_label = ctk.CTkLabel(
                card, 
                text=desc, 
                font=ctk.CTkFont(size=11),
                text_color=("gray60", "gray40"),
                wraplength=200
            )
            desc_label.pack(pady=5)
            
            # Make card clickable
            for widget in [card, icon_label, title_label, desc_label]:
                widget.bind("<Button-1>", lambda e, t=tab: self._switch_tab_animated(t))
                widget.bind("<Enter>", lambda e, c=card: c.configure(fg_color=("gray80", "gray25")))
                widget.bind("<Leave>", lambda e, c=card: c.configure(fg_color=("gray90", "gray20")))

    def _create_smart_planner_tab(self):
        frame = ctk.CTkScrollableFrame(self.tab_container, corner_radius=10)
        self.tabs["planner"] = frame
        
        # Header
        header = ctk.CTkFrame(frame, height=80, corner_radius=15)
        header.pack(fill="x", padx=10, pady=10)
        header.pack_propagate(False)
        
        ctk.CTkLabel(
            header,
            text="🧳Smart Itinerary Planner",
            font=ctk.CTkFont(size=22, weight="bold")
        ).pack(pady=25)
        
        # Input section
        input_section = ctk.CTkFrame(frame, corner_radius=15)
        input_section.pack(fill="x", padx=10, pady=10)
        
        # Create input grid
        self._create_planner_inputs(input_section)
        
        # Progress bar
        self.planner_progress = ctk.CTkProgressBar(frame, height=20, corner_radius=10)
        self.planner_progress.pack(fill="x", padx=10, pady=5)
        self.planner_progress.set(0)
        
        # Results section
        self.planner_results = ctk.CTkScrollableFrame(frame, height=400, corner_radius=15)
        self.planner_results.pack(fill="both", expand=True, padx=10, pady=10)

    def _create_planner_inputs(self, parent):
        # Left column
        left_frame = ctk.CTkFrame(parent, fg_color="transparent")
        left_frame.pack(side="left", fill="both", expand=True, padx=10, pady=15)
        
        # Date input
        date_frame = ctk.CTkFrame(left_frame, fg_color="transparent")
        date_frame.pack(fill="x", pady=5)
        
        ctk.CTkLabel(date_frame, text="📅 Travel Date:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.planner_date = ctk.CTkEntry(date_frame, height=35, corner_radius=8)
        self.planner_date.pack(fill="x", pady=2)
        self.planner_date.insert(0, datetime.now().strftime("%Y-%m-%d"))
        
        # Location inputs
        start_frame = ctk.CTkFrame(left_frame, fg_color="transparent")
        start_frame.pack(fill="x", pady=5)
        
        ctk.CTkLabel(start_frame, text="🚀 Start Location:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.planner_start = ctk.CTkComboBox(
            start_frame, 
            values=list(places_data.keys()),
            height=35,
            corner_radius=8,
            font=ctk.CTkFont(size=12)
        )
        self.planner_start.pack(fill="x", pady=2)
        
        end_frame = ctk.CTkFrame(left_frame, fg_color="transparent")
        end_frame.pack(fill="x", pady=5)
        
        ctk.CTkLabel(end_frame, text="🏁 End Location:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.planner_end = ctk.CTkComboBox(
            end_frame,
            values=list(places_data.keys()),
            height=35,
            corner_radius=8,
            font=ctk.CTkFont(size=12)
        )
        self.planner_end.pack(fill="x", pady=2)
        
        # Right column
        right_frame = ctk.CTkFrame(parent, fg_color="transparent")
        right_frame.pack(side="right", fill="both", expand=True, padx=10, pady=15)
        
        # Budget input
        budget_frame = ctk.CTkFrame(right_frame, fg_color="transparent")
        budget_frame.pack(fill="x", pady=5)
        
        ctk.CTkLabel(budget_frame, text="💰 Budget (₹):", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.planner_budget = ctk.CTkEntry(budget_frame, height=35, corner_radius=8)
        self.planner_budget.pack(fill="x", pady=2)
        self.planner_budget.insert(0, "1000")
        
        # Experience type
        exp_frame = ctk.CTkFrame(right_frame, fg_color="transparent")
        exp_frame.pack(fill="x", pady=5)
        
        ctk.CTkLabel(exp_frame, text="🎯 Experience Type:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.planner_experience = ctk.CTkComboBox(
            exp_frame,
            values=["Any", "Adventure", "Religious", "Market", "Nature", "Cultural", "Landmark", "Institution"],
            height=35,
            corner_radius=8
        )
        self.planner_experience.pack(fill="x", pady=2)
        
        # Options
        options_frame = ctk.CTkFrame(right_frame, fg_color="transparent")
        options_frame.pack(fill="x", pady=10)
        
        self.strict_budget_var = tk.BooleanVar()
        self.optimize_time_var = tk.BooleanVar()
        
        ctk.CTkCheckBox(options_frame, text="💸 Strict Budget", variable=self.strict_budget_var).pack(anchor="w", pady=2)
        ctk.CTkCheckBox(options_frame, text="⚡ Optimize for Time", variable=self.optimize_time_var).pack(anchor="w", pady=2)
        
        # Generate button
        generate_btn = ctk.CTkButton(
            parent,
            text="🚀 Generate Smart Itinerary",
            command=self._generate_smart_itinerary,
            height=45,
            corner_radius=12,
            font=ctk.CTkFont(size=16, weight="bold")
        )
        generate_btn.pack(pady=20)

    def _generate_smart_itinerary(self):
        """Enhanced itinerary generation with progress animation"""
        # Clear previous results
        for widget in self.planner_results.winfo_children():
            widget.destroy()
        
        # Start progress animation
        self._animate_progress(self.planner_progress, self._process_itinerary_generation)

    def _process_itinerary_generation(self):
        """Process itinerary generation with enhanced algorithms"""
        try:
            # Get inputs
            budget = int(self.planner_budget.get())
            date_str = self.planner_date.get()
            start_loc = self.planner_start.get()
            end_loc = self.planner_end.get()
            experience_type = self.planner_experience.get()
            
            if not start_loc or not end_loc:
                messagebox.showerror("Error", "Please select both start and end locations")
                return
            
            # Get weather with caching
            weather = self._get_cached_weather(date_str, places_data[start_loc].coords[0])
            
            # Find optimal route using A* algorithm
            route_info = self._find_route_astar(start_loc, end_loc)
            
            # Get smart recommendations using BST and heap
            recommendations = self._get_smart_recommendations(
                budget, experience_type, route_info, date_str
            )
            
            # Display results
            self._display_enhanced_results(weather, route_info, recommendations, budget)
            
        except ValueError:
            messagebox.showerror("Error", "Please enter a valid budget")
        except Exception as e:
            messagebox.showerror("Error", f"An error occurred: {str(e)}")

    def _find_route_astar(self, start: str, end: str) -> Route:
        """A* algorithm implementation for optimal pathfinding"""
        cache_key = f"{start}-{end}"
        if cache_key in self.route_cache:
            return self.route_cache[cache_key]
        
        def heuristic(a: str, b: str) -> float:
            """Euclidean distance heuristic"""
            coord_a = places_data[a].coords
            coord_b = places_data[b].coords
            return math.sqrt((coord_a[0] - coord_b[0])**2 + (coord_a[1] - coord_b[1])**2)
        
        # Priority queue: (f_score, g_score, node, path)
        open_set = [(0, 0, start, [start])]
        closed_set = set()
        g_scores = {start: 0}
        
        while open_set:
            f_score, g_score, current, path = heapq.heappop(open_set)
            
            if current in closed_set:
                continue
                
            if current == end:
                # Calculate route metrics
                total_distance = sum(
                    graph[path[i]][path[i+1]]["dist"] 
                    for i in range(len(path)-1)
                )
                total_time = sum(
                    graph[path[i]][path[i+1]]["time"] 
                    for i in range(len(path)-1)
                )
                total_cost = sum(places_data[place].cost for place in path)
                
                route = Route(path, total_distance, total_time, total_cost)
                self.route_cache[cache_key] = route
                return route
            
            closed_set.add(current)
            
            for neighbor, edge_data in graph.get(current, {}).items():
                if neighbor in closed_set:
                    continue
                
                tentative_g = g_score + edge_data["dist"] + edge_data["time"] * 0.1
                
                if neighbor not in g_scores or tentative_g < g_scores[neighbor]:
                    g_scores[neighbor] = tentative_g
                    f_score = tentative_g + heuristic(neighbor, end)
                    heapq.heappush(open_set, (f_score, tentative_g, neighbor, path + [neighbor]))
        
        # Fallback to simple path if A* fails
        return Route([start, end], 0, 0, 0)

    def _get_smart_recommendations(self, budget: int, experience_type: str, route_info: Route, date_str: str) -> List[Place]:
        """Enhanced recommendation system using BST and priority queue"""
        # Get places by rating range using BST
        high_rated_places = self.place_bst.search_by_rating_range(4.0, 5.0)
        
        # Filter by category and budget
        filtered_places = []
        for place in high_rated_places:
            if place.name in route_info.path:
                continue
            if experience_type != "Any" and place.category != experience_type:
                continue
            if place.cost <= budget:
                filtered_places.append(place)
        
        # Priority queue for recommendations (negative rating for max-heap behavior)
        recommendations_heap = []
        
        for place in filtered_places:
            # Calculate priority score
            base_score = place.rating
            
            # Boost score for places along the route
            route_boost = 1.2 if any(
                neighbor in route_info.path 
                for neighbor in graph.get(place.name, {})
            ) else 1.0
            
            # Time-based boost
            time_boost = 1.1 if self._is_good_time(place.name, date_str) else 0.9
            
            # Popularity boost
            popularity_boost = 1.0 + place.popularity_score * 0.2
            
            final_score = base_score * route_boost * time_boost * popularity_boost
            
            heapq.heappush(recommendations_heap, (-final_score, place))
        
        # Extract top recommendations
        recommendations = []
        total_cost = 0
        total_time = 0
        
        while recommendations_heap and len(recommendations) < 5:
            score, place = heapq.heappop(recommendations_heap)
            
            if (self.strict_budget_var.get() and total_cost + place.cost > budget):
                continue
            if total_time + place.visit_time > 10:
                continue
                
            recommendations.append(place)
            total_cost += place.cost
            total_time += place.visit_time
        
        return recommendations

    def _display_enhanced_results(self, weather: dict, route_info: Route, recommendations: List[Place], budget: int):
        """Display results with enhanced UI components"""
        # Weather card
        weather_card = ctk.CTkFrame(self.planner_results, corner_radius=15)
        weather_card.pack(fill="x", padx=10, pady=10)
        
        weather_header = ctk.CTkLabel(
            weather_card,
            text="🌤 Weather Forecast",
            font=ctk.CTkFont(size=16, weight="bold")
        )
        weather_header.pack(pady=10)
        
        weather_info = ctk.CTkLabel(
            weather_card,
            text=f"{weather['condition']} | {weather['temp_c']}°C | {weather['comment']}",
            font=ctk.CTkFont(size=14)
        )
        weather_info.pack(pady=5)
        
        # Route card
        route_card = ctk.CTkFrame(self.planner_results, corner_radius=15)
        route_card.pack(fill="x", padx=10, pady=10)
        
        route_header = ctk.CTkLabel(
            route_card,
            text="🛤 Optimal Route",
            font=ctk.CTkFont(size=16, weight="bold")
        )
        route_header.pack(pady=10)
        
        route_details = ctk.CTkLabel(
            route_card,
            text=f"Path: {' → '.join(route_info.path)}\n"
                 f"Distance: {route_info.distance} km | Time: {route_info.time} min\n"
                 f"Cost: ₹{route_info.cost}",
            font=ctk.CTkFont(size=12),
            justify="left"
        )
        route_details.pack(pady=5)
        
        # Recommendations cards
        if recommendations:
            rec_header = ctk.CTkLabel(
                self.planner_results,
                text="🎯 Smart Recommendations",
                font=ctk.CTkFont(size=18, weight="bold")
            )
            rec_header.pack(pady=15)
            
            for i, place in enumerate(recommendations):
                self._create_place_card(self.planner_results, place, i+1)

    def _create_place_card(self, parent, place: Place, index: int):
        """Create an enhanced place card"""
        card = ctk.CTkFrame(parent, corner_radius=12, height=120)
        card.pack(fill="x", padx=10, pady=5)
        card.pack_propagate(False)
        
        # Left side - Index and category icon
        left_frame = ctk.CTkFrame(card, width=80, fg_color="transparent")
        left_frame.pack(side="left", fill="y", padx=10, pady=10)
        left_frame.pack_propagate(False)
        
        index_label = ctk.CTkLabel(
            left_frame,
            text=str(index),
            font=ctk.CTkFont(size=24, weight="bold"),
            width=40,
            height=40,
            corner_radius=20,
            fg_color=("blue", "darkblue")
        )
        index_label.pack(pady=5)
        
        category_icons = {
            "Adventure": "🏔", "Religious": "🕉", "Market": "🛒",
            "Nature": "🌿", "Cultural": "🏛", "Landmark": "🏛",
            "Institution": "🎓"
        }
        
        icon_label = ctk.CTkLabel(
            left_frame,
            text=category_icons.get(place.category, "📍"),
            font=ctk.CTkFont(size=20)
        )
        icon_label.pack()
        
        # Right side - Place details
        right_frame = ctk.CTkFrame(card, fg_color="transparent")
        right_frame.pack(side="right", fill="both", expand=True, padx=10, pady=10)
        
        # Place name and rating
        name_frame = ctk.CTkFrame(right_frame, fg_color="transparent")
        name_frame.pack(fill="x")
        
        name_label = ctk.CTkLabel(
            name_frame,
            text=place.name,
            font=ctk.CTkFont(size=16, weight="bold"),
            anchor="w"
        )
        name_label.pack(side="left")
        
        rating_label = ctk.CTkLabel(
            name_frame,
            text=f"⭐ {place.rating}",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="orange"
        )
        rating_label.pack(side="right")
        
        # Details
        details_text = f"💰 ₹{place.cost} | ⏱ {place.visit_time}h | 📍 {place.category}"
        details_label = ctk.CTkLabel(
            right_frame,
            text=details_text,
            font=ctk.CTkFont(size=11),
            anchor="w",
            text_color=("gray60", "gray40")
        )
        details_label.pack(fill="x", pady=2)
        
        # Description
        desc_label = ctk.CTkLabel(
            right_frame,
            text=place.description,
            font=ctk.CTkFont(size=10),
            anchor="w",
            wraplength=400,
            text_color=("gray50", "gray50")
        )
        desc_label.pack(fill="x", pady=2)
        
        # Best time
        best_time = self._get_best_time(place.name)
        time_label = ctk.CTkLabel(
            right_frame,
            text=f"🕐 Best time: {best_time}",
            font=ctk.CTkFont(size=10),
            anchor="w",
            text_color=("green", "lightgreen")
        )
        time_label.pack(fill="x")

    def _create_weather_pro_tab(self):
        frame = ctk.CTkScrollableFrame(self.tab_container, corner_radius=10)
        self.tabs["weather"] = frame
        
        # Header
        header = ctk.CTkFrame(frame, height=80, corner_radius=15)
        header.pack(fill="x", padx=10, pady=10)
        header.pack_propagate(False)
        
        ctk.CTkLabel(
            header,
            text="🌤 Weather Forecasting",
            font=ctk.CTkFont(size=22, weight="bold")
        ).pack(pady=25)
        
        # Input section
        input_frame = ctk.CTkFrame(frame, corner_radius=15)
        input_frame.pack(fill="x", padx=10, pady=10)
        
        # Location and date inputs
        inputs_grid = ctk.CTkFrame(input_frame, fg_color="transparent")
        inputs_grid.pack(fill="x", padx=20, pady=20)
        
        # Location
        loc_frame = ctk.CTkFrame(inputs_grid, fg_color="transparent")
        loc_frame.pack(side="left", fill="both", expand=True, padx=10)
        
        ctk.CTkLabel(loc_frame, text="📍 Location:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.weather_location = ctk.CTkComboBox(
            loc_frame,
            values=list(places_data.keys()),
            height=35,
            corner_radius=8
        )
        self.weather_location.pack(fill="x", pady=5)
        
        # Date
        date_frame = ctk.CTkFrame(inputs_grid, fg_color="transparent")
        date_frame.pack(side="right", fill="both", expand=True, padx=10)
        
        ctk.CTkLabel(date_frame, text="📅 Date:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.weather_date = ctk.CTkEntry(date_frame, height=35, corner_radius=8)
        self.weather_date.pack(fill="x", pady=5)
        self.weather_date.insert(0, datetime.now().strftime("%Y-%m-%d"))
        
        # Buttons
        btn_frame = ctk.CTkFrame(input_frame, fg_color="transparent")
        btn_frame.pack(pady=15)
        
        ctk.CTkButton(
            btn_frame,
            text="🔍 Get Forecast",
            command=self._get_weather_forecast,
            height=40,
            corner_radius=10,
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack(side="left", padx=5)
        
        ctk.CTkButton(
            btn_frame,
            text="📊 7-Day Forecast",
            command=self._get_extended_forecast,
            height=40,
            corner_radius=10,
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack(side="left", padx=5)
        
        # Results area
        self.weather_results = ctk.CTkFrame(frame, corner_radius=15)
        self.weather_results.pack(fill="both", expand=True, padx=10, pady=10)

    def _get_weather_forecast(self):
        """Get weather forecast"""
        location = self.weather_location.get()
        date_str = self.weather_date.get()
        
        if not location:
            messagebox.showerror("Error", "Please select a location")
            return
        
        # Clear previous results
        for widget in self.weather_results.winfo_children():
            widget.destroy()
        
        try:
            weather = self._get_cached_weather(date_str, places_data[location].coords[0])
            self._create_weather_display(self.weather_results, location, date_str, weather)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to get weather: {str(e)}")

    def _create_weather_display(self, parent, location: str, date_str: str, weather: dict):
        """Create weather display"""
        # Main weather card
        main_card = ctk.CTkFrame(parent, corner_radius=15, height=200)
        main_card.pack(fill="x", padx=20, pady=20)
        main_card.pack_propagate(False)
        
        # Left side - Main info
        left_frame = ctk.CTkFrame(main_card, fg_color="transparent")
        left_frame.pack(side="left", fill="both", expand=True, padx=20, pady=20)
        
        location_label = ctk.CTkLabel(
            left_frame,
            text=f"📍 {location}",
            font=ctk.CTkFont(size=18, weight="bold")
        )
        location_label.pack(anchor="w")
        
        date_label = ctk.CTkLabel(
            left_frame,
            text=f"📅 {date_str}",
            font=ctk.CTkFont(size=14),
            text_color=("gray60", "gray40")
        )
        date_label.pack(anchor="w", pady=2)
        
        condition_label = ctk.CTkLabel(
            left_frame,
            text=weather['condition'],
            font=ctk.CTkFont(size=24, weight="bold")
        )
        condition_label.pack(anchor="w", pady=10)
        
        # Right side - Temperature
        right_frame = ctk.CTkFrame(main_card, fg_color="transparent")
        right_frame.pack(side="right", fill="y", padx=20, pady=20)
        
        temp_label = ctk.CTkLabel(
            right_frame,
            text=f"{weather['temp_c']}°C",
            font=ctk.CTkFont(size=36, weight="bold"),
            text_color="orange"
        )
        temp_label.pack()
        
        temp_f_label = ctk.CTkLabel(
            right_frame,
            text=f"({weather['temp_f']}°F)",
            font=ctk.CTkFont(size=14),
            text_color=("gray60", "gray40")
        )
        temp_f_label.pack()
        
        # Recommendation card
        rec_card = ctk.CTkFrame(parent, corner_radius=15)
        rec_card.pack(fill="x", padx=20, pady=10)
        
        ctk.CTkLabel(
            rec_card,
            text="💡 Travel Recommendation",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=10)
        
        ctk.CTkLabel(
            rec_card,
            text=weather['comment'],
            font=ctk.CTkFont(size=14),
            wraplength=600
        ).pack(pady=10)

    def _get_extended_forecast(self):
        """Generate 7-day weather forecast"""
        location = self.weather_location.get()
        if not location:
            messagebox.showerror("Error", "Please select a location")
            return
        
        # Clear previous results
        for widget in self.weather_results.winfo_children():
            widget.destroy()
        
        # Generate 7-day forecast
        forecasts = []
        base_date = datetime.now()
        
        for i in range(7):
            date = base_date + timedelta(days=i)
            date_str = date.strftime("%Y-%m-%d")
            weather = self._get_cached_weather(date_str, places_data[location].coords[0])
            forecasts.append((date_str, weather))
        
        # Create forecast display
        self._create_extended_forecast_display(self.weather_results, location, forecasts)

    def _create_extended_forecast_display(self, parent, location: str, forecasts: list):
        """Create 7-day forecast display with data cards instead of graph"""
        # Header
        header = ctk.CTkLabel(
            parent,
            text=f"📊 7-Day Forecast for {location}",
            font=ctk.CTkFont(size=18, weight="bold")
        )
        header.pack(pady=20)
        
        # Create forecast cards
        forecast_container = ctk.CTkScrollableFrame(parent, corner_radius=15)
        forecast_container.pack(fill="both", expand=True, padx=20, pady=10)
        
        for i, (date_str, weather) in enumerate(forecasts):
            # Parse date for better display
            date_obj = datetime.strptime(date_str, "%Y-%m-%d")
            day_name = date_obj.strftime("%A")
            formatted_date = date_obj.strftime("%B %d")
            
            # Create forecast card
            forecast_card = ctk.CTkFrame(forecast_container, corner_radius=12, height=100)
            forecast_card.pack(fill="x", padx=10, pady=5)
            forecast_card.pack_propagate(False)
            
            # Left side - Date info
            left_frame = ctk.CTkFrame(forecast_card, width=150, fg_color="transparent")
            left_frame.pack(side="left", fill="y", padx=15, pady=15)
            left_frame.pack_propagate(False)
            
            day_label = ctk.CTkLabel(
                left_frame,
                text=day_name,
                font=ctk.CTkFont(size=16, weight="bold")
            )
            day_label.pack(anchor="w")
            
            date_label = ctk.CTkLabel(
                left_frame,
                text=formatted_date,
                font=ctk.CTkFont(size=12),
                text_color=("gray60", "gray40")
            )
            date_label.pack(anchor="w")
            
            # Center - Weather condition
            center_frame = ctk.CTkFrame(forecast_card, fg_color="transparent")
            center_frame.pack(side="left", fill="both", expand=True, padx=10, pady=15)
            
            condition_label = ctk.CTkLabel(
                center_frame,
                text=weather['condition'],
                font=ctk.CTkFont(size=14, weight="bold")
            )
            condition_label.pack()
            
            comment_label = ctk.CTkLabel(
                center_frame,
                text=weather['comment'],
                font=ctk.CTkFont(size=10),
                text_color=("gray60", "gray40"),
                wraplength=200
            )
            comment_label.pack(pady=2)
            
            # Right side - Temperature
            right_frame = ctk.CTkFrame(forecast_card, width=100, fg_color="transparent")
            right_frame.pack(side="right", fill="y", padx=15, pady=15)
            right_frame.pack_propagate(False)
            
            temp_label = ctk.CTkLabel(
                right_frame,
                text=f"{weather['temp_c']}°C",
                font=ctk.CTkFont(size=20, weight="bold"),
                text_color="orange"
            )
            temp_label.pack()
            
            temp_f_label = ctk.CTkLabel(
                right_frame,
                text=f"({weather['temp_f']}°F)",
                font=ctk.CTkFont(size=10),
                text_color=("gray60", "gray40")
            )
            temp_f_label.pack()
        
        # Summary card
        summary_card = ctk.CTkFrame(forecast_container, corner_radius=15)
        summary_card.pack(fill="x", padx=10, pady=15)
        
        ctk.CTkLabel(
            summary_card,
            text="📈 Weekly Summary",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=10)
        
        # Calculate summary statistics
        temps = [w['temp_c'] for _, w in forecasts]
        avg_temp = sum(temps) / len(temps)
        max_temp = max(temps)
        min_temp = min(temps)
        
        summary_text = f"""
Average Temperature: {avg_temp:.1f}°C
Highest Temperature: {max_temp}°C
Lowest Temperature: {min_temp}°C
        """
        
        ctk.CTkLabel(
            summary_card,
            text=summary_text.strip(),
            font=ctk.CTkFont(size=12),
            justify="left"
        ).pack(pady=10)

    def _create_parking_ai_tab(self):
        frame = ctk.CTkScrollableFrame(self.tab_container, corner_radius=10)
        self.tabs["parking"] = frame
        
        # Header
        header = ctk.CTkFrame(frame, height=80, corner_radius=15)
        header.pack(fill="x", padx=10, pady=10)
        header.pack_propagate(False)
        
        ctk.CTkLabel(
            header,
            text="🅿 Parking- Smart Availability Prediction",
            font=ctk.CTkFont(size=22, weight="bold")
        ).pack(pady=25)
        
        # Input section
        input_frame = ctk.CTkFrame(frame, corner_radius=15)
        input_frame.pack(fill="x", padx=10, pady=10)
        
        # Location selection
        loc_frame = ctk.CTkFrame(input_frame, fg_color="transparent")
        loc_frame.pack(pady=20)
        
        ctk.CTkLabel(
            loc_frame,
            text="📍 Select Location:",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=10)
        
        self.parking_location = ctk.CTkComboBox(
            loc_frame,
            values=list(places_data.keys()),
            height=40,
            corner_radius=10,
            font=ctk.CTkFont(size=14),
            width=300
        )
        self.parking_location.pack(pady=10)
        
        # Check button
        ctk.CTkButton(
            input_frame,
            text="🔍 Check Availability",
            command=self._check_parking_availability,
            height=45,
            corner_radius=12,
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=15)
        
        # Results area
        self.parking_results = ctk.CTkFrame(frame, corner_radius=15)
        self.parking_results.pack(fill="both", expand=True, padx=10, pady=10)

    def _check_parking_availability(self):
        """Check parking availability with prediction"""
        location = self.parking_location.get()
        if not location:
            messagebox.showerror("Error", "Please select a location")
            return
        
        # Clear previous results
        for widget in self.parking_results.winfo_children():
            widget.destroy()
        
        # Get parking data
        parking_data = self._get_parking_data()
        
        if location not in parking_data:
            ctk.CTkLabel(
                self.parking_results,
                text=f"No parking data available for {location}",
                font=ctk.CTkFont(size=14)
            ).pack(pady=20)
            return
        
        data = parking_data[location]
        prediction = self._predict_parking_availability(data)
        
        # Create parking display
        self._create_parking_display(self.parking_results, location, data, prediction)

    def _get_parking_data(self):
        """Get parking data"""
        return {
            "Clock Tower": {
                "capacity": 60, "peak_times": [(10,14), (17,20)], 
                "popularity": 0.9, "weekend_multiplier": 2.0,
                "hourly_rates": [5, 5, 5, 5, 5, 5, 10, 15, 15, 15, 20, 20, 20, 20, 15, 15, 20, 25, 25, 20, 15, 10, 5, 5],
                "facilities": ["CCTV", "Security", "Covered"]
            },
            "Robber's Cave": {
                "capacity": 120, "peak_times": [(11,16)], 
                "popularity": 0.8, "weekend_multiplier": 2.5,
                "hourly_rates": [10, 10, 10, 10, 10, 10, 15, 20, 20, 25, 30, 35, 35, 30, 25, 20, 15, 15, 15, 15, 10, 10, 10, 10],
                "facilities": ["Restrooms", "Food Court", "ATM"]
            },
            "Paltan Bazaar": {
                "capacity": 50, "peak_times": [(11,15), (17,21)], 
                "popularity": 0.95, "weekend_multiplier": 2.3,
                "hourly_rates": [10, 10, 10, 10, 10, 10, 15, 20, 25, 30, 35, 40, 40, 35, 30, 25, 30, 35, 40, 35, 30, 25, 20, 15],
                "facilities": ["Shopping Access", "Food Court", "ATM"]
            }
        }

    def _predict_parking_availability(self, data: dict) -> dict:
        """AI-like parking availability prediction"""
        now = datetime.now()
        current_hour = now.hour
        is_weekend = now.weekday() >= 5
        
        # Base occupancy calculation
        base_occupancy = data["capacity"] * data["popularity"]
        
        # Weekend adjustment
        if is_weekend:
            base_occupancy *= data["weekend_multiplier"]
        
        # Peak time adjustment
        in_peak = any(start <= current_hour <= end for start, end in data["peak_times"])
        if in_peak:
            base_occupancy *= 1.4
        
        # Calculate availability
        occupied = min(data["capacity"], int(base_occupancy))
        available = data["capacity"] - occupied
        occupancy_percent = (occupied / data["capacity"]) * 100
        
        # Determine status
        if occupancy_percent < 50:
            status = "🟢 Available"
            status_color = "green"
        elif occupancy_percent < 80:
            status = "🟡 Limited"
            status_color = "orange"
        else:
            status = "🔴 Full"
            status_color = "red"
        
        return {
            "status": status,
            "status_color": status_color,
            "available": available,
            "occupied": occupied,
            "capacity": data["capacity"],
            "occupancy_percent": occupancy_percent,
            "current_rate": data["hourly_rates"][current_hour],
            "facilities": data["facilities"]
        }

    def _create_parking_display(self, parent, location: str, data: dict, prediction: dict):
        """Create parking availability display"""
        # Main status card
        status_card = ctk.CTkFrame(parent, corner_radius=15, height=150)
        status_card.pack(fill="x", padx=20, pady=20)
        status_card.pack_propagate(False)
        
        # Left side - Status
        left_frame = ctk.CTkFrame(status_card, fg_color="transparent")
        left_frame.pack(side="left", fill="both", expand=True, padx=20, pady=20)
        
        location_label = ctk.CTkLabel(
            left_frame,
            text=f"🅿 {location}",
            font=ctk.CTkFont(size=20, weight="bold")
        )
        location_label.pack(anchor="w")
        
        status_label = ctk.CTkLabel(
            left_frame,
            text=prediction["status"],
            font=ctk.CTkFont(size=18, weight="bold"),
            text_color=prediction["status_color"]
        )
        status_label.pack(anchor="w", pady=5)
        
        availability_label = ctk.CTkLabel(
            left_frame,
            text=f"Available: {prediction['available']}/{prediction['capacity']} spaces",
            font=ctk.CTkFont(size=14)
        )
        availability_label.pack(anchor="w")
        
        # Right side - Details
        right_frame = ctk.CTkFrame(status_card, fg_color="transparent")
        right_frame.pack(side="right", fill="y", padx=20, pady=20)
        
        # Occupancy progress bar
        occupancy_frame = ctk.CTkFrame(right_frame, fg_color="transparent")
        occupancy_frame.pack(fill="x")
        
        ctk.CTkLabel(
            occupancy_frame,
            text=f"Occupancy: {prediction['occupancy_percent']:.1f}%",
            font=ctk.CTkFont(size=12, weight="bold")
        ).pack()
        
        occupancy_bar = ctk.CTkProgressBar(occupancy_frame, height=15, corner_radius=8)
        occupancy_bar.pack(fill="x", pady=5)
        occupancy_bar.set(prediction['occupancy_percent'] / 100)
        
        # Rate
        rate_label = ctk.CTkLabel(
            right_frame,
            text=f"💰 Current Rate: ₹{prediction['current_rate']}/hour",
            font=ctk.CTkFont(size=12)
        )
        rate_label.pack(pady=5)

    def _create_voice_translator_tab(self):
        frame = ctk.CTkScrollableFrame(self.tab_container, corner_radius=10)
        self.tabs["translator"] = frame
        
        # Header
        header = ctk.CTkFrame(frame, height=80, corner_radius=15)
        header.pack(fill="x", padx=10, pady=10)
        header.pack_propagate(False)
        
        ctk.CTkLabel(
            header,
            text="🗣 Translator ",
            font=ctk.CTkFont(size=22, weight="bold")
        ).pack(pady=25)
        
        # Language selection
        lang_frame = ctk.CTkFrame(frame, corner_radius=15)
        lang_frame.pack(fill="x", padx=10, pady=10)
        
        lang_grid = ctk.CTkFrame(lang_frame, fg_color="transparent")
        lang_grid.pack(fill="x", padx=20, pady=20)
        
        # From language
        from_frame = ctk.CTkFrame(lang_grid, fg_color="transparent")
        from_frame.pack(side="left", fill="both", expand=True, padx=10)
        
        ctk.CTkLabel(from_frame, text="🌐 From:", font=ctk.CTkFont(size=16, weight="bold")).pack(anchor="w")
        self.translator_from = ctk.CTkComboBox(
            from_frame,
            values=["English", "Hindi", "Spanish", "French", "German"],
            height=35,
            corner_radius=8
        )
        self.translator_from.pack(fill="x", pady=5)
        self.translator_from.set("English")
        
        # Swap button
        swap_frame = ctk.CTkFrame(lang_grid, fg_color="transparent", width=60)
        swap_frame.pack(side="left", padx=10)
        swap_frame.pack_propagate(False)
        
        ctk.CTkButton(
            swap_frame,
            text="🔄",
            command=self._swap_languages,
            width=50,
            height=35,
            corner_radius=25,
            font=ctk.CTkFont(size=16)
        ).pack(pady=20)
        
        # To language
        to_frame = ctk.CTkFrame(lang_grid, fg_color="transparent")
        to_frame.pack(side="right", fill="both", expand=True, padx=10)
        
        ctk.CTkLabel(to_frame, text="🎯 To:", font=ctk.CTkFont(size=16, weight="bold")).pack(anchor="w")
        self.translator_to = ctk.CTkComboBox(
            to_frame,
            values=["Hindi", "English", "Spanish", "French", "German"],
            height=35,
            corner_radius=8
        )
        self.translator_to.pack(fill="x", pady=5)
        self.translator_to.set("Hindi")
        
        # Input section
        input_frame = ctk.CTkFrame(frame, corner_radius=15)
        input_frame.pack(fill="x", padx=10, pady=10)
        
        ctk.CTkLabel(
            input_frame,
            text="💬 Input Text or Use Voice:",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=15)
        
        self.translator_input = ctk.CTkTextbox(input_frame, height=100, corner_radius=10)
        self.translator_input.pack(fill="x", padx=20, pady=10)
        
        # Control buttons
        control_frame = ctk.CTkFrame(input_frame, fg_color="transparent")
        control_frame.pack(pady=15)
        
        ctk.CTkButton(
            control_frame,
            text="🎤 Voice Input",
            command=self._voice_input,
            height=40,
            corner_radius=10,
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack(side="left", padx=10)
        
        ctk.CTkButton(
            control_frame,
            text="🔄 Translate",
            command=self._translate_enhanced,
            height=40,
            corner_radius=10,
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack(side="left", padx=10)
        
        ctk.CTkButton(
            control_frame,
            text="🗑 Clear",
            command=self._clear_translation,
            height=40,
            corner_radius=10,
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack(side="left", padx=10)
        
        # Output section
        output_frame = ctk.CTkFrame(frame, corner_radius=15)
        output_frame.pack(fill="x", padx=10, pady=10)
        
        ctk.CTkLabel(
            output_frame,
            text="✨ Translation Result:",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=15)
        
        self.translator_output = ctk.CTkTextbox(output_frame, height=100, corner_radius=10)
        self.translator_output.pack(fill="x", padx=20, pady=10)
        
        # Common phrases section
        self._create_common_phrases_section(frame)

    def _create_common_phrases_section(self, parent):
        """Create common phrases section for quick translation"""
        phrases_frame = ctk.CTkFrame(parent, corner_radius=15)
        phrases_frame.pack(fill="x", padx=10, pady=10)
        
        ctk.CTkLabel(
            phrases_frame,
            text="🚀 Quick Phrases:",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=15)
        
        # Common travel phrases
        phrases = [
            "Hello, how are you?",
            "Where is the nearest restaurant?",
            "How much does this cost?",
            "Can you help me?",
            "Thank you very much",
            "Where is the bathroom?",
            "I need a taxi",
            "What time is it?"
        ]
        
        # Create phrase buttons in a grid
        phrases_grid = ctk.CTkFrame(phrases_frame, fg_color="transparent")
        phrases_grid.pack(fill="x", padx=20, pady=10)
        
        for i, phrase in enumerate(phrases):
            row = i // 2
            col = i % 2
            
            phrase_btn = ctk.CTkButton(
                phrases_grid,
                text=phrase,
                command=lambda p=phrase: self._use_quick_phrase(p),
                height=35,
                corner_radius=8,
                font=ctk.CTkFont(size=12)
            )
            phrase_btn.grid(row=row, column=col, padx=5, pady=5, sticky="ew")
            
            # Configure grid weights
            phrases_grid.grid_columnconfigure(col, weight=1)

    def _use_quick_phrase(self, phrase: str):
        """Use a quick phrase for translation"""
        self.translator_input.delete("1.0", "end")
        self.translator_input.insert("1.0", phrase)
        self._translate_enhanced()

    def _swap_languages(self):
        """Swap source and target languages"""
        from_lang = self.translator_from.get()
        to_lang = self.translator_to.get()
        
        self.translator_from.set(to_lang)
        self.translator_to.set(from_lang)
        
        # Also swap the text if there's content
        input_text = self.translator_input.get("1.0", "end").strip()
        output_text = self.translator_output.get("1.0", "end").strip()
        
        if input_text and output_text:
            self.translator_input.delete("1.0", "end")
            self.translator_input.insert("1.0", output_text)

    def _voice_input(self):
        """Voice input with error handling"""
        try:
            self.translator_output.delete("1.0", "end")
            self.translator_output.insert("1.0", "🎤 Listening... Please speak clearly")
            self.root.update()
            
            with sr.Microphone() as source:
                # Adjust for ambient noise
                self.recognizer.adjust_for_ambient_noise(source, duration=1)
                
                # Listen for audio
                audio = self.recognizer.listen(source, timeout=10, phrase_time_limit=10)
                
                self.translator_output.delete("1.0", "end")
                self.translator_output.insert("1.0", "🔄 Processing speech...")
                self.root.update()
                
                # Recognize speech
                text = self.recognizer.recognize_google(audio)
                
                # Insert recognized text
                self.translator_input.delete("1.0", "end")
                self.translator_input.insert("1.0", text)
                
                self.translator_output.delete("1.0", "end")
                self.translator_output.insert("1.0", f"✅ Recognized: {text}")
                
                # Auto-translate
                self._translate_enhanced()
                
        except sr.WaitTimeoutError:
            self.translator_output.delete("1.0", "end")
            self.translator_output.insert("1.0", "⏰ Timeout: No speech detected")
        except sr.UnknownValueError:
            self.translator_output.delete("1.0", "end")
            self.translator_output.insert("1.0", "❌ Could not understand audio. Please try again.")
        except Exception as e:
            self.translator_output.delete("1.0", "end")
            self.translator_output.insert("1.0", f"❌ Error: {str(e)}")

    def _translate_enhanced(self):
        """Enhanced translation with caching"""
        try:
            text = self.translator_input.get("1.0", "end").strip()
            if not text:
                messagebox.showwarning("Warning", "Please enter text to translate")
                return
            
            from_lang = self.translator_from.get()
            to_lang = self.translator_to.get()
            
            # Check cache first
            cache_key = f"{text}_{from_lang}_{to_lang}"
            if hasattr(self, 'translation_cache') and cache_key in self.translation_cache:
                result = self.translation_cache[cache_key]
                self.translator_output.delete("1.0", "end")
                self.translator_output.insert("1.0", result)
                return
            
            # Show processing
            self.translator_output.delete("1.0", "end")
            self.translator_output.insert("1.0", "🔄 Translating...")
            self.root.update()
            
            # Language code mapping
            lang_codes = {
                "English": "en", "Hindi": "hi", "Spanish": "es",
                "French": "fr", "German": "de"
            }
            
            src_code = lang_codes.get(from_lang, "en")
            dest_code = lang_codes.get(to_lang, "hi")
            
            try:
                # Try Google Translator
                translator = GoogleTranslator(source=src_code, target=dest_code)
                result = translator.translate(text)
                
                if not result:
                    raise Exception("Translation returned empty result")
                    
            except:
                # Fallback to basic translations
                result = self._get_fallback_translation(text, from_lang, to_lang)
            
            # Cache the result
            if not hasattr(self, 'translation_cache'):
                self.translation_cache = {}
            self.translation_cache[cache_key] = result
            
            # Display result
            self.translator_output.delete("1.0", "end")
            self.translator_output.insert("1.0", result)
            
        except Exception as e:
            self.translator_output.delete("1.0", "end")
            self.translator_output.insert("1.0", f"❌ Translation failed: {str(e)}")

    def _get_fallback_translation(self, text: str, from_lang: str, to_lang: str) -> str:
        """Fallback translation for common phrases"""
        fallback_translations = {
            ("English", "Hindi"): {
                "hello": "नमस्ते", "hello, how are you?": "नमस्ते, आप कैसे हैं?",
                "thank you": "धन्यवाद", "thank you very much": "बहुत धन्यवाद",
                "where is the nearest restaurant?": "सबसे नजदीकी रेस्टोरेंट कहाँ है?",
                "how much does this cost?": "इसकी कीमत कितनी है?",
                "can you help me?": "क्या आप मेरी मदद कर सकते हैं?",
                "where is the bathroom?": "बाथरूम कहाँ है?",
                "i need a taxi": "मुझे टैक्सी चाहिए",
                "what time is it?": "समय क्या है?"
            },
            ("Hindi", "English"): {
                "नमस्ते": "hello", "आप कैसे हैं": "how are you",
                "धन्यवाद": "thank you", "बहुत धन्यवाद": "thank you very much",
                "सबसे नजदीकी रेस्टोरेंट कहाँ है": "where is the nearest restaurant",
                "इसकी कीमत कितनी है": "how much does this cost",
                "क्या आप मेरी मदद कर सकते हैं": "can you help me",
                "बाथरूम कहाँ है": "where is the bathroom",
                "मुझे टैक्सी चाहिए": "i need a taxi",
                "समय क्या है": "what time is it"
            }
        }
        
        key = (from_lang, to_lang)
        if key in fallback_translations:
            return fallback_translations[key].get(text.lower(), "Translation not available")
        
        return "Translation service unavailable"

    def _clear_translation(self):
        """Clear translation input and output"""
        self.translator_input.delete("1.0", "end")
        self.translator_output.delete("1.0", "end")

    def _create_route_optimizer_tab(self):
        frame = ctk.CTkScrollableFrame(self.tab_container, corner_radius=10)
        self.tabs["route"] = frame
        
        # Header
        header = ctk.CTkFrame(frame, height=80, corner_radius=15)
        header.pack(fill="x", padx=10, pady=10)
        header.pack_propagate(False)
        
        ctk.CTkLabel(
            header,
            text="🧭 Route Optimizer - A* Pathfinding Algorithm",
            font=ctk.CTkFont(size=22, weight="bold")
        ).pack(pady=25)
        
        # Input section
        input_frame = ctk.CTkFrame(frame, corner_radius=15)
        input_frame.pack(fill="x", padx=10, pady=10)
        
        # Route inputs
        route_grid = ctk.CTkFrame(input_frame, fg_color="transparent")
        route_grid.pack(fill="x", padx=20, pady=20)
        
        # Start location
        start_frame = ctk.CTkFrame(route_grid, fg_color="transparent")
        start_frame.pack(side="left", fill="both", expand=True, padx=10)
        
        ctk.CTkLabel(start_frame, text="🚀 Start Location:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.route_start = ctk.CTkComboBox(
            start_frame,
            values=list(places_data.keys()),
            height=35,
            corner_radius=8
        )
        self.route_start.pack(fill="x", pady=5)
        
        # End location
        end_frame = ctk.CTkFrame(route_grid, fg_color="transparent")
        end_frame.pack(side="right", fill="both", expand=True, padx=10)
        
        ctk.CTkLabel(end_frame, text="🏁 End Location:", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        self.route_end = ctk.CTkComboBox(
            end_frame,
            values=list(places_data.keys()),
            height=35,
            corner_radius=8
        )
        self.route_end.pack(fill="x", pady=5)
        
        # Options (simplified - removed elevation options)
        options_frame = ctk.CTkFrame(input_frame, fg_color="transparent")
        options_frame.pack(fill="x", padx=20, pady=10)
        
        self.optimize_distance_var = tk.BooleanVar(value=True)
        self.optimize_time_var = tk.BooleanVar()
        
        ctk.CTkCheckBox(options_frame, text="📏 Optimize for Distance", variable=self.optimize_distance_var).pack(side="left", padx=10)
        ctk.CTkCheckBox(options_frame, text="⚡ Optimize for Time", variable=self.optimize_time_var).pack(side="left", padx=10)
        
        # Buttons
        btn_frame = ctk.CTkFrame(input_frame, fg_color="transparent")
        btn_frame.pack(pady=15)
        
        ctk.CTkButton(
            btn_frame,
            text="🔍 Find Optimal Route",
            command=self._find_optimal_route,
            height=45,
            corner_radius=12,
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(side="left", padx=10)
        
        ctk.CTkButton(
            btn_frame,
            text="🗺 Show on Map",
            command=self._show_route_on_map,
            height=45,
            corner_radius=12,
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(side="left", padx=10)
        
        # Progress bar
        self.route_progress = ctk.CTkProgressBar(frame, height=20, corner_radius=10)
        self.route_progress.pack(fill="x", padx=10, pady=5)
        self.route_progress.set(0)
        
        # Results section
        self.route_results = ctk.CTkFrame(frame, corner_radius=15)
        self.route_results.pack(fill="both", expand=True, padx=10, pady=10)

    def _find_optimal_route(self):
        """Find optimal route with A* algorithm"""
        start = self.route_start.get()
        end = self.route_end.get()
        
        if not start or not end:
            messagebox.showerror("Error", "Please select both start and end locations")
            return
        
        if start == end:
            messagebox.showerror("Error", "Start and end locations cannot be the same")
            return
        
        # Clear previous results
        for widget in self.route_results.winfo_children():
            widget.destroy()
        
        # Start progress animation
        self._animate_progress(self.route_progress, lambda: self._process_route_finding(start, end))

    def _process_route_finding(self, start: str, end: str):
        """Process route finding"""
        try:
            # Find route using A* algorithm
            route_info = self._find_route_astar_simple(start, end)
            
            # Display results
            self._display_route_results(route_info)
            
        except Exception as e:
            messagebox.showerror("Error", f"Route calculation failed: {str(e)}")

    def _find_route_astar_simple(self, start: str, end: str) -> Route:
        """Simplified A* algorithm without elevation"""
        def heuristic(a: str, b: str) -> float:
            coord_a = places_data[a].coords
            coord_b = places_data[b].coords
            return math.sqrt((coord_a[0] - coord_b[0])**2 + (coord_a[1] - coord_b[1])**2)
        
        def calculate_cost(current: str, neighbor: str, edge_data: dict) -> float:
            cost = 0
            
            if self.optimize_distance_var.get():
                cost += edge_data["dist"] * 1.0
            
            if self.optimize_time_var.get():
                cost += edge_data["time"] * 0.1
            
            return cost if cost > 0 else edge_data["dist"]
        
        # A* implementation
        open_set = [(0, 0, start, [start])]
        closed_set = set()
        g_scores = {start: 0}
        
        while open_set:
            f_score, g_score, current, path = heapq.heappop(open_set)
            
            if current in closed_set:
                continue
            
            if current == end:
                # Calculate final metrics
                total_distance = sum(
                    graph[path[i]][path[i+1]]["dist"] 
                    for i in range(len(path)-1)
                )
                total_time = sum(
                    graph[path[i]][path[i+1]]["time"] 
                    for i in range(len(path)-1)
                )
                total_cost = sum(places_data[place].cost for place in path)
                
                return Route(path, total_distance, total_time, total_cost)
            
            closed_set.add(current)
            
            for neighbor, edge_data in graph.get(current, {}).items():
                if neighbor in closed_set:
                    continue
                
                tentative_g = g_score + calculate_cost(current, neighbor, edge_data)
                
                if neighbor not in g_scores or tentative_g < g_scores[neighbor]:
                    g_scores[neighbor] = tentative_g
                    f_score = tentative_g + heuristic(neighbor, end)
                    heapq.heappush(open_set, (f_score, tentative_g, neighbor, path + [neighbor]))
        
        # Fallback
        return Route([start, end], 0, 0, 0)

    def _display_route_results(self, route_info: Route):
        """Display route results"""
        # Route summary card
        summary_card = ctk.CTkFrame(self.route_results, corner_radius=15, height=150)
        summary_card.pack(fill="x", padx=20, pady=20)
        summary_card.pack_propagate(False)
        
        # Left side - Route path
        left_frame = ctk.CTkFrame(summary_card, fg_color="transparent")
        left_frame.pack(side="left", fill="both", expand=True, padx=20, pady=20)
        
        path_label = ctk.CTkLabel(
            left_frame,
            text="🛤 Optimal Route:",
            font=ctk.CTkFont(size=16, weight="bold")
        )
        path_label.pack(anchor="w")
        
        route_path = " → ".join(route_info.path)
        path_text = ctk.CTkLabel(
            left_frame,
            text=route_path,
            font=ctk.CTkFont(size=14),
            wraplength=400
        )
        path_text.pack(anchor="w", pady=5)
        
        # Right side - Metrics
        right_frame = ctk.CTkFrame(summary_card, fg_color="transparent")
        right_frame.pack(side="right", fill="y", padx=20, pady=20)
        
        metrics_text = f"""📏 Distance: {route_info.distance} km
⏱ Time: {route_info.time} minutes
💰 Cost: ₹{route_info.cost}"""
        
        metrics_label = ctk.CTkLabel(
            right_frame,
            text=metrics_text,
            font=ctk.CTkFont(size=12),
            justify="left"
        )
        metrics_label.pack()
        
        # Step-by-step directions
        self._create_step_directions(self.route_results, route_info)

    def _create_step_directions(self, parent, route_info: Route):
        """Create step-by-step directions"""
        directions_frame = ctk.CTkFrame(parent, corner_radius=15)
        directions_frame.pack(fill="x", padx=20, pady=10)
        
        ctk.CTkLabel(
            directions_frame,
            text="📋 Step-by-Step Directions",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(pady=15)
        
        directions_list = ctk.CTkScrollableFrame(directions_frame, height=200)
        directions_list.pack(fill="both", expand=True, padx=15, pady=10)
        
        for i in range(len(route_info.path) - 1):
            current = route_info.path[i]
            next_place = route_info.path[i + 1]
            
            if next_place in graph.get(current, {}):
                edge_data = graph[current][next_place]
                
                step_frame = ctk.CTkFrame(directions_list, corner_radius=8)
                step_frame.pack(fill="x", pady=5)
                
                step_text = f"{i+1}. From {current} to {next_place}\n"
                step_text += f"   📏 {edge_data['dist']} km • ⏱ {edge_data['time']} min"
                
                ctk.CTkLabel(
                    step_frame,
                    text=step_text,
                    font=ctk.CTkFont(size=12),
                    anchor="w",
                    justify="left"
                ).pack(fill="x", padx=10, pady=8)

    def _show_route_on_map(self):
        """Show the calculated route on an interactive map"""
        start = self.route_start.get()
        end = self.route_end.get()
        
        if not start or not end:
            messagebox.showwarning("Warning", "Please select start and end locations first")
            return
        
        try:
            route_info = self._find_route_astar_simple(start, end)
            self._generate_route_map(route_info)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to show route on map: {str(e)}")

    def _create_interactive_map_tab(self):
        frame = ctk.CTkScrollableFrame(self.tab_container, corner_radius=10)
        self.tabs["map"] = frame
        
        # Header
        header = ctk.CTkFrame(frame, height=80, corner_radius=15)
        header.pack(fill="x", padx=10, pady=10)
        header.pack_propagate(False)
        
        ctk.CTkLabel(
            header,
            text="📍 Interactive Map - Explore Dehradun",
            font=ctk.CTkFont(size=22, weight="bold")
        ).pack(pady=25)
        
        # Map controls (simplified - removed heatmap and cluster)
        controls_frame = ctk.CTkFrame(frame, corner_radius=15)
        controls_frame.pack(fill="x", padx=10, pady=10)
        
        # Filter controls
        filter_frame = ctk.CTkFrame(controls_frame, fg_color="transparent")
        filter_frame.pack(fill="x", padx=20, pady=15)
        
        ctk.CTkLabel(
            filter_frame,
            text="🎯 Filter Places:",
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack(anchor="w")
        
        filter_options = ctk.CTkFrame(filter_frame, fg_color="transparent")
        filter_options.pack(fill="x", pady=10)
        
        # Category filter
        self.map_category_filter = ctk.CTkComboBox(
            filter_options,
            values=["All Categories", "Adventure", "Religious", "Market", "Nature", "Cultural", "Landmark", "Institution"],
            height=35,
            corner_radius=8
        )
        self.map_category_filter.pack(side="left", padx=10)
        self.map_category_filter.set("All Categories")
        
        # Rating filter
        self.map_rating_filter = ctk.CTkComboBox(
            filter_options,
            values=["All Ratings", "4.5+ Stars", "4.0+ Stars", "3.5+ Stars"],
            height=35,
            corner_radius=8
        )
        self.map_rating_filter.pack(side="left", padx=10)
        self.map_rating_filter.set("All Ratings")
        
        # Cost filter
        self.map_cost_filter = ctk.CTkComboBox(
            filter_options,
            values=["All Costs", "Free", "Under ₹50", "Under ₹100", "Under ₹200"],
            height=35,
            corner_radius=8
        )
        self.map_cost_filter.pack(side="left", padx=10)
        self.map_cost_filter.set("All Costs")
        
        # Map action button (simplified)
        btn_frame = ctk.CTkFrame(controls_frame, fg_color="transparent")
        btn_frame.pack(pady=15)
        
        ctk.CTkButton(
            btn_frame,
            text="🗺 Show All Places",
            command=self._show_filtered_map,
            height=45,
            corner_radius=12,
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack()
        
        # Map info section
        info_frame = ctk.CTkFrame(frame, corner_radius=15)
        info_frame.pack(fill="both", expand=True, padx=10, pady=10)
        
        self.map_info_label = ctk.CTkLabel(
            info_frame,
            text="🗺 Interactive maps will open in your default web browser\n📍 Click on markers for detailed information\n🎯 Use filters to customize your view",
            font=ctk.CTkFont(size=14),
            justify="center"
        )
        self.map_info_label.pack(expand=True)

    def _show_filtered_map(self):
        """Show map with applied filters"""
        try:
            # Get filter values
            category_filter = self.map_category_filter.get()
            rating_filter = self.map_rating_filter.get()
            cost_filter = self.map_cost_filter.get()
            
            # Filter places
            filtered_places = self._apply_map_filters(category_filter, rating_filter, cost_filter)
            
            # Create map
            self._generate_filtered_map(filtered_places)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to generate map: {str(e)}")

    def _apply_map_filters(self, category_filter: str, rating_filter: str, cost_filter: str) -> Dict[str, Place]:
        """Apply filters to places"""
        filtered = {}
        
        for name, place in places_data.items():
            # Category filter
            if category_filter != "All Categories" and place.category != category_filter:
                continue
            
            # Rating filter
            if rating_filter == "4.5+ Stars" and place.rating < 4.5:
                continue
            elif rating_filter == "4.0+ Stars" and place.rating < 4.0:
                continue
            elif rating_filter == "3.5+ Stars" and place.rating < 3.5:
                continue
            
            # Cost filter
            if cost_filter == "Free" and place.cost > 0:
                continue
            elif cost_filter == "Under ₹50" and place.cost >= 50:
                continue
            elif cost_filter == "Under ₹100" and place.cost >= 100:
                continue
            elif cost_filter == "Under ₹200" and place.cost >= 200:
                continue
            
            filtered[name] = place
        
        return filtered

    def _generate_filtered_map(self, filtered_places: Dict[str, Place]):
        """Generate map with filtered places"""
        if not filtered_places:
            messagebox.showinfo("Info", "No places match the selected filters")
            return
        
        # Create map centered on Dehradun
        map_obj = folium.Map(
            location=[30.3256, 78.0437],
            zoom_start=12,
            tiles="cartodbpositron"
        )
        
        # Color mapping for categories
        category_colors = {
            "Adventure": "green", "Religious": "purple", "Market": "red",
            "Nature": "darkgreen", "Cultural": "orange", "Landmark": "blue",
            "Institution": "gray"
        }
        
        # Add markers for filtered places
        for name, place in filtered_places.items():
            color = category_colors.get(place.category, "blue")
            
            # Create detailed popup
            popup_html = f"""
            <div style="width: 250px;">
                <h4 style="margin: 0; color: #333;">{name}</h4>
                <hr style="margin: 5px 0;">
                <p style="margin: 2px 0;"><b>Category:</b> {place.category}</p>
                <p style="margin: 2px 0;"><b>Rating:</b> ⭐ {place.rating}/5.0</p>
                <p style="margin: 2px 0;"><b>Cost:</b> ₹{place.cost}</p>
                <p style="margin: 2px 0;"><b>Visit Time:</b> {place.visit_time} hours</p>
                <hr style="margin: 5px 0;">
                <p style="margin: 2px 0; font-size: 12px;">{place.description}</p>
            </div>
            """
            
            folium.Marker(
                location=place.coords,
                popup=folium.Popup(popup_html, max_width=300),
                tooltip=f"{name} ({place.category})",
                icon=folium.Icon(color=color, icon="info-sign")
            ).add_to(map_obj)
        
        # Save and open map
        temp_path = os.path.join(tempfile.gettempdir(), "dehradun_filtered_map.html")
        map_obj.save(temp_path)
        webbrowser.open(f"file://{temp_path}")

    def _generate_route_map(self, route_info: Route):
        """Generate route map"""
        try:
            if len(route_info.path) < 2:
                messagebox.showerror("Error", "Route needs at least 2 points")
                return
            
            # Get coordinates for the route
            coords = [places_data[location].coords for location in route_info.path]
            
            # Create map centered on the route
            center_lat = sum(coord[0] for coord in coords) / len(coords)
            center_lon = sum(coord[1] for coord in coords) / len(coords)
            
            map_obj = folium.Map(
                location=[center_lat, center_lon],
                zoom_start=13,
                tiles="cartodbpositron"
            )
            
            # Add route markers
            for i, (location, coord) in enumerate(zip(route_info.path, coords)):
                place = places_data[location]
                
                # Different icons for start, end, and waypoints
                if i == 0:
                    icon_color = "green"
                    icon_symbol = "play"
                elif i == len(route_info.path) - 1:
                    icon_color = "red"
                    icon_symbol = "stop"
                else:
                    icon_color = "blue"
                    icon_symbol = "info-sign"
                
                # Detailed popup
                popup_html = f"""
                <div style="width: 250px;">
                    <h4>{location}</h4>
                    <p><b>Step:</b> {i+1} of {len(route_info.path)}</p>
                    <p><b>Category:</b> {place.category}</p>
                    <p><b>Rating:</b> ⭐ {place.rating}</p>
                    <p><b>Cost:</b> ₹{place.cost}</p>
                    <p><b>Visit Time:</b> {place.visit_time} hours</p>
                    <hr>
                    <p>{place.description}</p>
                </div>
                """
                
                folium.Marker(
                    location=coord,
                    popup=folium.Popup(popup_html, max_width=300),
                    tooltip=f"{i+1}. {location}",
                    icon=folium.Icon(color=icon_color, icon=icon_symbol)
                ).add_to(map_obj)
            
            # Add route line
            folium.PolyLine(
                locations=coords,
                color="blue",
                weight=5,
                opacity=0.8,
                dash_array="10, 5"
            ).add_to(map_obj)
            
            # Save and open
            temp_path = os.path.join(tempfile.gettempdir(), "dehradun_route.html")
            map_obj.save(temp_path)
            webbrowser.open(f"file://{temp_path}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Route map failed: {str(e)}")

    # Helper methods
    def _toggle_theme(self):
        """Toggle between dark and light themes"""
        if self.current_theme == "dark":
            self.current_theme = "light"
            ctk.set_appearance_mode("light")
        else:
            self.current_theme = "dark"
            ctk.set_appearance_mode("dark")

    def _update_clock(self):
        """Update the real-time clock"""
        current_time = datetime.now().strftime("%H:%M:%S")
        self.clock_label.configure(text=f"🕐 {current_time}")
        self.root.after(1000, self._update_clock)

    def _switch_tab_animated(self, tab_id):
        """Switch tabs with animation effect"""
        # Hide all tabs
        for tab_frame in self.tabs.values():
            tab_frame.pack_forget()
        
        # Show selected tab
        if tab_id in self.tabs:
            self.tabs[tab_id].pack(fill="both", expand=True, padx=10, pady=10)
        
        # Update button states
        for btn_id, btn in self.nav_buttons.items():
            if btn_id == tab_id:
                btn.configure(fg_color=("blue", "darkblue"))
            else:
                btn.configure(fg_color=("gray75", "gray25"))

    def _animate_progress(self, progress_bar, callback):
        """Animate progress bar and execute callback"""
        def animate():
            for i in range(101):
                progress_bar.set(i / 100)
                self.root.update()
                time.sleep(0.02)
            callback()
        
        threading.Thread(target=animate, daemon=True).start()

    def _get_cached_weather(self, date_str: str, lat: float) -> dict:
        """Get weather with caching for better performance"""
        cache_key = f"{date_str}_{lat}"
        if cache_key in self.weather_cache:
            return self.weather_cache[cache_key]
        
        weather = self._get_weather_report(date_str, lat)
        self.weather_cache[cache_key] = weather
        return weather

    def _get_weather_report(self, date_str: str, lat: float) -> dict:
        """Generate deterministic weather report"""
        try:
            date = datetime.strptime(date_str, "%Y-%m-%d")
            seed = int(hashlib.sha256(f"{date_str}{lat}".encode()).hexdigest(), 16)
            random.seed(seed)
            
            month = date.month
            if 3 <= month <= 5:
                base_temp = random.randint(25, 35)
                conditions = ["Clear ☀", "Hot 🔥", "Partly Cloudy ⛅"]
            elif 6 <= month <= 9:
                base_temp = random.randint(20, 30)
                conditions = ["Rainy 🌧", "Thunderstorm ⛈", "Humid 💧"]
            else:
                base_temp = random.randint(10, 20)
                conditions = ["Clear ☀", "Foggy 🌫", "Cold ❄"]
            
            condition = random.choice(conditions)
            temp_c = base_temp + random.randint(-2, 2)
            temp_f = (temp_c * 9/5) + 32
            
            recommendations = {
                "Clear ☀": "Perfect for outdoor activities!",
                "Hot 🔥": "Stay hydrated and wear sunscreen",
                "Partly Cloudy ⛅": "Good for sightseeing",
                "Rainy 🌧": "Carry an umbrella",
                "Thunderstorm ⛈": "Avoid open areas",
                "Humid 💧": "Wear light clothing",
                "Foggy 🌫": "Drive carefully",
                "Cold ❄": "Wear warm clothing"
            }
            
            return {
                "condition": condition,
                "temp_c": temp_c,
                "temp_f": temp_f,
                "comment": recommendations[condition]
            }
        except:
            return {
                "condition": "Clear ☀",
                "temp_c": 25,
                "temp_f": 77,
                "comment": "Perfect for outdoor activities!"
            }

    def _is_good_time(self, place: str, date_str: str) -> bool:
        """Determine if it's a good time to visit a place"""
        try:
            date = datetime.strptime(date_str, "%Y-%m-%d")
            is_weekend = date.weekday() >= 5
            place_category = places_data[place].category
            
            if is_weekend and place_category in ["Nature", "Landmark", "Adventure", "Market"]:
                return True
            if not is_weekend and place_category in ["Cultural", "Institution"]:
                return True
            return False
        except:
            return True

    def _get_best_time(self, place: str) -> str:
        """Get the best time to visit a place"""
        coords = places_data[place].coords[0]
        category = places_data[place].category
        
        if category in ["Nature", "Adventure"]:
            return "Morning (8-11 AM)"
        elif category == "Religious":
            return "Early Morning (6-9 AM)"
        elif category == "Cultural":
            return "Afternoon (2-5 PM)"
        elif category == "Market":
            return "Evening (5-8 PM)"
        elif coords >= 30.4:
            return "Morning (7-10 AM)"
        else:
            return "Evening (5-8 PM)"

    def _start_background_updates(self):
        """Start background updates for real-time features"""
        pass

if __name__ == "__main__":
    root = ctk.CTk()
    app = SimplifiedTravelGuideApp(root)
    root.mainloop()
