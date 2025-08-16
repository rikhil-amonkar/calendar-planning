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
        "Tallinn": (18, 20),
        "Milan": (24, 26),
        "Riga": (5, 8)
    }
    
    direct_flights = [
        ("Riga", "Prague"), ("Stockholm", "Milan"), ("Riga", "Milan"),
        ("Lisbon", "Stockholm"), ("Stockholm", "Santorini"), ("Naples", "Warsaw"),
        ("Lisbon", "Warsaw"), ("Naples", "Milan"), ("Lisbon", "Naples"),
        ("Riga", "Tallinn"), ("Tallinn", "Prague"), ("Stockholm", "Warsaw"),
        ("Riga", "Warsaw"), ("Lisbon", "Riga"), ("Riga", "Stockholm"),
        ("Lisbon", "Porto"), ("Lisbon", "Prague"), ("Milan", "Porto"),
        ("Prague", "Milan"), ("Lisbon", "Milan"), ("Warsaw", "Porto"),
        ("Warsaw", "Tallinn"), ("Santorini", "Milan"), ("Stockholm", "Prague"),
        ("Stockholm", "Tallinn"), ("Warsaw", "Milan"), ("Santorini", "Naples"),
        ("Warsaw", "Prague")
    ]
    
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
    
    # Go to Santorini after Naples
    add_to_itinerary("Santorini", 5)
    
    # Go to Lisbon after Santorini
    add_to_itinerary("Lisbon", 5)
    
    # Go to Porto after Lisbon
    add_to_itinerary("Porto", 3)
    
    # Go to Stockholm after Porto
    add_to_itinerary("Stockholm", 2)
    
    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary(), indent=4))