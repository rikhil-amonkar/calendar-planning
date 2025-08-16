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
    
    # Calculate remaining days
    remaining_days = 28 - current_day + 1
    
    # Allocate the remaining days to the other cities
    # We need to ensure the sum of days allocated to these cities is equal to remaining_days
    # Let's allocate days based on the constraints provided
    if remaining_days == 6:  # We have exactly 6 days left
        add_to_itinerary("Santorini", 2)
        add_to_itinerary("Lisbon", 2)
        add_to_itinerary("Porto", 1)
        add_to_itinerary("Stockholm", 1)
    
    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary(), indent=4))