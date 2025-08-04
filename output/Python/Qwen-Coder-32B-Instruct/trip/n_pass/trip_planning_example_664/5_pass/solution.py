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
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Place Bucharest first within the visit window
    start_bucharest = max(constraints["Bucharest"]["visit_window"][0], current_day)
    end_bucharest = start_bucharest + constraints["Bucharest"]["days"] - 1
    if end_bucharest > 18:
        raise ValueError("Cannot place Bucharest within the given constraints without exceeding 18 days")
    itinerary.append({"day_range": f"Day {start_bucharest}-{end_bucharest}", "place": "Bucharest"})
    current_day = end_bucharest + 1
    
    # Attend the wedding in Munich within the wedding window
    start_munich_wedding = max(constraints["Munich"]["wedding_window"][0], current_day)
    end_munich_wedding = start_munich_wedding + constraints["Munich"]["days"] - 1
    if end_munich_wedding > 18:
        raise ValueError("Cannot place Munich within the given constraints without exceeding 18 days")
    itinerary.append({"day_range": f"Day {start_munich_wedding}-{end_munich_wedding}", "place": "Munich"})
    current_day = end_munich_wedding + 1
    
    # Meet friends in Seville within the meet friends window
    start_seville_friends = max(constraints["Seville"]["meet_friends_window"][0], current_day)
    end_seville_friends = start_seville_friends + constraints["Seville"]["days"] - 1
    if end_seville_friends > 18:
        raise ValueError("Cannot place Seville within the given constraints without exceeding 18 days")
    itinerary.append({"day_range": f"Day {start_seville_friends}-{end_seville_friends}", "place": "Seville"})
    current_day = end_seville_friends + 1
    
    # Stay in Milan for 2 days
    start_milan = current_day
    end_milan = start_milan + constraints["Milan"]["days"] - 1
    if end_milan > 18:
        raise ValueError("Cannot place Milan within the given constraints without exceeding 18 days")
    itinerary.append({"day_range": f"Day {start_milan}-{end_milan}", "place": "Milan"})
    current_day = end_milan + 1
    
    # Stay in Stockholm for 5 days
    start_stockholm = current_day
    end_stockholm = start_stockholm + constraints["Stockholm"]["days"] - 1
    if end_stockholm > 18:
        raise ValueError("Cannot place Stockholm within the given constraints without exceeding 18 days")
    itinerary.append({"day_range": f"Day {start_stockholm}-{end_stockholm}", "place": "Stockholm"})
    current_day = end_stockholm + 1
    
    # Stay in Tallinn for the remaining days to make it exactly 18 days
    if current_day <= 18:
        start_tallinn = current_day
        end_tallinn = min(start_tallinn + constraints["Tallinn"]["days"] - 1, 18)
        itinerary.append({"day_range": f"Day {start_tallinn}-{end_tallinn}", "place": "Tallinn"})
        current_day = end_tallinn + 1
    
    # Ensure the total duration is exactly 18 days
    if current_day != 19:
        raise ValueError(f"Itinerary does not reach or exceed 18 days, it reaches {current_day - 1} days")
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))