import json

# Define the cities and their required stay durations
cities = {
    "Brussels": 4,
    "Bucharest": 3,
    "Stuttgart": 4,
    "Mykonos": 2,
    "Madrid": 2,
    "Helsinki": 5,
    "Split": 3,
    "London": 5
}

# Define the fixed events
fixed_events = {
    "Stuttgart": (1, 4),  # Meeting between day 1 and day 4
    "Madrid": (20, 21)    # Conference on day 20 and day 21
}

# Direct flight connections
direct_flights = {
    "Helsinki": ["London", "Madrid", "Brussels", "Split"],
    "London": ["Helsinki", "Madrid", "Brussels", "Bucharest", "Stuttgart", "Mykonos", "Split"],
    "Madrid": ["Helsinki", "London", "Bucharest", "Split", "Mykonos"],
    "Brussels": ["Helsinki", "London", "Bucharest", "Madrid"],
    "Bucharest": ["Brussels", "London", "Madrid"],
    "Stuttgart": ["London", "Split"],
    "Mykonos": ["London", "Madrid"],
    "Split": ["Helsinki", "London", "Madrid", "Stuttgart"]
}

def can_transition(city1, city2):
    return city2 in direct_flights[city1]

def generate_itinerary():
    itinerary = []
    current_day = 1
    current_city = "Helsinki"  # Starting point
    
    # Initial stay in Helsinki
    itinerary.append({"day_range": f"Day {current_day}-{current_day+4}", "place": "Helsinki"})
    current_day += 5
    
    # Move to Brussels (overlapping with Helsinki)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+3}", "place": "Brussels"})
    current_day += 4
    
    # Move to Bucharest (overlapping with Brussels)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+2}", "place": "Bucharest"})
    current_day += 3
    
    # Move to London (overlapping with Bucharest)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+4}", "place": "London"})
    current_day += 5
    
    # Move to Stuttgart (overlapping with London)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+3}", "place": "Stuttgart"})
    current_day += 4
    
    # Move to Mykonos (overlapping with London)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+1}", "place": "Mykonos"})
    current_day += 2
    
    # Move back to Madrid (conference days)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+1}", "place": "Madrid"})
    current_day += 2
    
    # Extend stay in Madrid for the conference
    itinerary[-1]["day_range"] = f"Day {current_day-2}-{current_day}"
    
    # Move to Split (overlapping with Madrid)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+2}", "place": "Split"})
    current_day += 3
    
    # Adjust last days to fit within 21 days
    itinerary[-1]["day_range"] = f"Day {current_day-2}-Day 21"
    
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary = generate_itinerary()
print(json.dumps(itinerary, indent=4))