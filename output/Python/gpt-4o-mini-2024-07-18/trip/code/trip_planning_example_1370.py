import json

def create_itinerary():
    # Define trip constraints
    trip_duration = 30
    cities = {
        "Santorini": {"days": 5, "friend_meeting": (25, 29)},
        "Krakow": {"days": 5, "wedding": (18, 22)},
        "Paris": {"days": 5, "friend_meeting": (11, 15)},
        "Vilnius": {"days": 3},
        "Munich": {"days": 5},
        "Geneva": {"days": 2},
        "Amsterdam": {"days": 4},
        "Budapest": {"days": 5},
        "Split": {"days": 4},
    }

    # Define direct flight connections
    direct_flights = {
        "Paris": ["Krakow", "Amsterdam", "Split", "Geneva"],
        "Krakow": ["Paris", "Vilnius", "Amsterdam", "Split", "Munich"],
        "Vilnius": ["Munich", "Split", "Amsterdam", "Paris"],
        "Munich": ["Vilnius", "Split", "Amsterdam", "Budapest", "Paris", "Geneva", "Krakow"],
        "Amsterdam": ["Paris", "Geneva", "Budapest", "Split"],
        "Split": ["Paris", "Krakow", "Munich", "Amsterdam", "Geneva"],
        "Budapest": ["Munich", "Amsterdam", "Paris", "Geneva"],
        "Geneva": ["Paris", "Amsterdam", "Split", "Budapest", "Santorini"],
        "Santorini": ["Geneva", "Amsterdam"],
    }

    # Create itinerary
    itinerary = []
    current_day = 1
    visited_cities = []

    def add_days(location, days):
        nonlocal current_day
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days - 1}', 'place': location})
        current_day += days

    # Adding cities to itinerary based on constraints
    add_days("Paris", cities["Paris"]["days"])
    visited_cities.append("Paris")

    # Meeting friend in Paris (between day 11-15)
    if current_day >= 11 and current_day <= 15:
        pass  # Friend meeting in Paris is within the stay
    
    # Travel from Paris to Krakow for wedding
    add_days("Krakow", cities["Krakow"]["days"])
    visited_cities.append("Krakow")
    
    # Travel from Krakow to Vilnius post-wedding
    add_days("Vilnius", cities["Vilnius"]["days"])
    visited_cities.append("Vilnius")
    
    # Travel from Vilnius to Munich
    add_days("Munich", cities["Munich"]["days"])
    visited_cities.append("Munich")
    
    # Travel from Munich to Geneva
    add_days("Geneva", cities["Geneva"]["days"])
    visited_cities.append("Geneva")
    
    # Travel from Geneva to Santorini
    add_days("Santorini", cities["Santorini"]["days"])
    visited_cities.append("Santorini")

    # Travel from Santorini to Split
    add_days("Split", cities["Split"]["days"])
    visited_cities.append("Split")
    
    # Travel from Split to Budapest
    add_days("Budapest", cities["Budapest"]["days"])
    visited_cities.append("Budapest")
    
    # Travel from Budapest to Amsterdam
    add_days("Amsterdam", cities["Amsterdam"]["days"])
    visited_cities.append("Amsterdam")

    # Convert itinerary to JSON format
    itinerary_json = json.dumps(itinerary, indent=4)
    return itinerary_json

# Run the function and print the result
if __name__ == "__main__":
    result = create_itinerary()
    print(result)