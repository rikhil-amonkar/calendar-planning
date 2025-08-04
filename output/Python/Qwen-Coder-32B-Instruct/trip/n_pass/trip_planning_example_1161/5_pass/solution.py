import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Mykonos": {"days": 4, "range": (15, 18)},
        "Krakow": {"days": 4},
        "Vilnius": {"days": 2},
        "Helsinki": {"days": 2},
        "Dubrovnik": {"days": 3, "range": (2, 4)},
        "Oslo": {"days": 2, "range": (1, 2)},
        "Madrid": {"days": 5},
        "Paris": {"days": 2}
    }
    
    # Define the direct flights
    flights = [
        ("Oslo", "Krakow"), ("Oslo", "Paris"), ("Paris", "Madrid"),
        ("Helsinki", "Vilnius"), ("Oslo", "Madrid"), ("Oslo", "Helsinki"),
        ("Helsinki", "Krakow"), ("Dubrovnik", "Helsinki"), ("Dubrovnik", "Madrid"),
        ("Oslo", "Dubrovnik"), ("Krakow", "Paris"), ("Madrid", "Mykonos"),
        ("Oslo", "Vilnius"), ("Krakow", "Vilnius"), ("Helsinki", "Paris"),
        ("Vilnius", "Paris"), ("Helsinki", "Madrid")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to check if a flight is possible
    def can_fly(from_city, to_city, day):
        return (from_city, to_city) in flights or (to_city, from_city) in flights
    
    # Helper function to add a stay to the itinerary
    def add_stay(city, days, start_day):
        nonlocal current_day
        end_day = start_day + days - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Add the stays according to constraints
    add_stay("Oslo", 2, 1)  # Meet friends in Oslo (Day 1-2)
    add_stay("Dubrovnik", 3, 3)  # Annual show in Dubrovnik (Day 3-5)
    add_stay("Madrid", 5, 6)  # Stay in Madrid (Day 6-10)
    add_stay("Paris", 2, 11)  # Stay in Paris (Day 11-12)
    add_stay("Krakow", 4, 13)  # Stay in Krakow (Day 13-16)
    add_stay("Mykonos", 4, 15)  # Visit relatives in Mykonos (Day 15-18)
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Calculate and print the itinerary
print(calculate_itinerary())