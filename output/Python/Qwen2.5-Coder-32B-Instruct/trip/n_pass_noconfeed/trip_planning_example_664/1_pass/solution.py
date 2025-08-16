import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Tallinn": {"days": 2},
        "Bucharest": {"days": 4, "visit_window": (1, 4)},
        "Seville": {"days": 5, "meet_friends_window": (8, 12)},
        "Stockholm": {"days": 5},
        "Munich": {"days": 5, "wedding_window": (4, 8)},
        "Milan": {"days": 2}
    }
    
    # Define the direct flight connections
    flights = {
        "Milan": ["Stockholm", "Munich"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Milan", "Bucharest", "Seville", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Place Bucharest first due to the visit window constraint
    start_bucharest = max(1, current_day)
    end_bucharest = start_bucharest + constraints["Bucharest"]["days"] - 1
    itinerary.append({"day_range": f"Day {start_bucharest}-{end_bucharest}", "place": "Bucharest"})
    current_day = end_bucharest + 1
    
    # Place Munich next due to the wedding window constraint
    start_munich = max(current_day, constraints["Bucharest"]["wedding_window"][0])
    end_munich = start_munich + constraints["Munich"]["days"] - 1
    itinerary.append({"day_range": f"Day {start_munich}-{end_munich}", "place": "Munich"})
    current_day = end_munich + 1
    
    # Place Seville next due to the meet friends window constraint
    start_seville = max(current_day, constraints["Munich"]["meet_friends_window"][0])
    end_seville = start_seville + constraints["Seville"]["days"] - 1
    itinerary.append({"day_range": f"Day {start_seville}-{end_seville}", "place": "Seville"})
    current_day = end_seville + 1
    
    # Place Milan next
    start_milan = current_day
    end_milan = start_milan + constraints["Milan"]["days"] - 1
    itinerary.append({"day_range": f"Day {start_milan}-{end_milan}", "place": "Milan"})
    current_day = end_milan + 1
    
    # Place Stockholm next
    start_stockholm = current_day
    end_stockholm = start_stockholm + constraints["Stockholm"]["days"] - 1
    itinerary.append({"day_range": f"Day {start_stockholm}-{end_stockholm}", "place": "Stockholm"})
    current_day = end_stockholm + 1
    
    # Place Tallinn last
    start_tallinn = current_day
    end_tallinn = start_tallinn + constraints["Tallinn"]["days"] - 1
    itinerary.append({"day_range": f"Day {start_tallinn}-{end_tallinn}", "place": "Tallinn"})
    current_day = end_tallinn + 1
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))