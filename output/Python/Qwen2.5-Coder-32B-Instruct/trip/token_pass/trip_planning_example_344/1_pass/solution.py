import json

def generate_itinerary():
    # Define the constraints
    constraints = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6,
        "visit_relatives_athens": (1, 6),
        "attend_wedding_naples": (16, 20)
    }
    
    # Flight connections (direct flights)
    flights = {
        ("Valencia", "Naples"), ("Valencia", "Athens"),
        ("Athens", "Naples"), ("Zurich", "Naples"),
        ("Athens", "Zurich"), ("Zurich", "Valencia")
    }
    
    # Initialize the itinerary
    itinerary = []
    
    # Day 1-6: Athens (visit relatives)
    itinerary.append({"day_range": "Day 1-6", "place": "Athens"})
    current_day = 7
    
    # Day 7-15: Naples (transition from Athens to Naples)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Naples'] - 6}", "place": "Naples"})
    current_day += constraints['Naples'] - 5
    
    # Day 16-20: Naples (attend wedding)
    itinerary.append({"day_range": "Day 16-20", "place": "Naples"})
    current_day = 21
    
    # Day 21-26: Zurich (transition from Naples to Zurich)
    # Since the trip is only 20 days, we stop at day 20
    itinerary.append({"day_range": f"Day 21-{constraints['Zurich'] + 20 - 21}", "place": "Zurich"})
    
    # Output the itinerary in JSON format
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())