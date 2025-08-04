import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Vienna": (1, 4, 4),
        "Milan": (None, None, 2),
        "Rome": (None, None, 3),
        "Riga": (None, None, 2),
        "Lisbon": (11, 13, 3),
        "Vilnius": (None, None, 4),
        "Oslo": (13, 15, 3)
    }
    
    # Define the direct flights
    direct_flights = {
        "Riga": ["Oslo", "Milan", "Lisbon", "Vilnius"],
        "Oslo": ["Riga", "Rome", "Milan", "Vienna", "Lisbon", "Vilnius"],
        "Rome": ["Oslo", "Milan", "Lisbon", "Riga"],
        "Vienna": ["Milan", "Vilnius", "Lisbon", "Riga", "Oslo", "Rome"],
        "Milan": ["Vienna", "Oslo", "Riga", "Rome", "Lisbon"],
        "Lisbon": ["Vienna", "Riga", "Oslo", "Rome", "Milan"],
        "Vilnius": ["Riga", "Oslo", "Vienna"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Function to add a stay to the itinerary
    def add_stay(city, start_day, duration):
        nonlocal current_day
        end_day = start_day + duration - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Add Vienna stay
    add_stay("Vienna", constraints["Vienna"][0], constraints["Vienna"][2])
    
    # Add Milan stay
    add_stay("Milan", current_day, constraints["Milan"][2])
    
    # Add Rome stay
    add_stay("Rome", current_day, constraints["Rome"][2])
    
    # Add Riga stay
    add_stay("Riga", current_day, constraints["Riga"][2])
    
    # Add Lisbon stay
    add_stay("Lisbon", constraints["Lisbon"][0], constraints["Lisbon"][2])
    
    # Add Vilnius stay
    add_stay("Vilnius", current_day, constraints["Vilnius"][2])
    
    # Add Oslo stay
    add_stay("Oslo", constraints["Oslo"][0], constraints["Oslo"][2])
    
    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Calculate and print the itinerary
print(calculate_itinerary())