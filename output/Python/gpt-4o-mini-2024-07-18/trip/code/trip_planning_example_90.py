import json

def generate_trip_itinerary():
    # Define trip constraints
    cities = {
        "Vilnius": 7,
        "Naples": 5,
        "Vienna": 7
    }
    
    # Calculate day distributions based on constraints
    itinerary = []

    # Days in Naples
    itinerary.append({'day_range': 'Day 1-5', 'place': 'Naples'})
    
    # Travel from Naples to Vienna
    itinerary.append({'flying': 'Day 5-5', 'from': 'Naples', 'to': 'Vienna'})
    
    # Days in Vienna
    itinerary.append({'day_range': 'Day 5-12', 'place': 'Vienna'})
    
    # Travel from Vienna to Vilnius
    itinerary.append({'flying': 'Day 12-12', 'from': 'Vienna', 'to': 'Vilnius'})
    
    # Days in Vilnius
    itinerary.append({'day_range': 'Day 12-18', 'place': 'Vilnius'})
    
    # Finish the trip overview
    return json.dumps(itinerary, indent=4)

# Generate and print the trip itinerary
trip_itinerary_json = generate_trip_itinerary()
print(trip_itinerary_json)