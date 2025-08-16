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
    
    def add_to_itinerary(city, days):
        nonlocal current_day
        end_day = current_day + days - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Start with Riga for the show
    add_to_itinerary("Riga", 4)
    
    # Go to Tallinn after Riga show
    add_to_itinerary("Tallinn", 3)
    
    # Go to Warsaw after Tallinn
    add_to_itinerary("Warsaw", 2)
    
    # Go to Prague after Warsaw
    add_to_itinerary("Prague", 5)
    
    # Go to Milan for the meeting
    add_to_itinerary("Milan", 3)
    
    # Go to Naples after Milan meeting
    add_to_itinerary("Naples", 5)
    
    # Adjust the remaining days for Santorini, Lisbon, Porto, and Stockholm
    remaining_days = 28 - current_day + 1
    
    # Allocate days to each city proportionally or based on preference
    # Let's allocate 4 days to Santorini, 4 days to Lisbon, 3 days to Porto, and 2 days to Stockholm
    if remaining_days >= 14:  # Ensure we have enough days left
        add_to_itinerary("Santorini", 4)
        add_to_itinerary("Lisbon", 4)
        add_to_itinerary("Porto", 3)
        add_to_itinerary("Stockholm", 2)
    
    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary(), indent=4))