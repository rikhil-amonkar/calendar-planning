import json

def calculate_itinerary():
    constraints = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }
    
    fixed_dates = {
        "Tallinn": (5, 7),  # Day 5-7
        "Milan": (15, 17),   # Day 15-17
        "Riga": (1, 4)     # Day 1-4
    }
    
    itinerary = []
    current_day = 1
    
    def add_to_itinerary(city, start_day, end_day):
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    # Add fixed date cities first
    for city, (start, end) in fixed_dates.items():
        add_to_itinerary(city, start, end)
        current_day = end + 1
    
    # Add other cities according to their constraints
    remaining_cities = [city for city in constraints.keys() if city not in fixed_dates]
    
    for city in remaining_cities:
        days = constraints[city]
        add_to_itinerary(city, current_day, current_day + days - 1)
        current_day += days
    
    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary(), indent=4))