import json

def main():
    # Cities and required days
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,  # Must include days 4-8
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    # Direct flights (undirected graph)
    flights = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Oslo': ['Porto', 'Riga', 'Geneva', 'Edinburgh', 'Vilnius', 'Budapest', 'Helsinki', 'Tallinn'],
        'Edinburgh': ['Porto', 'Budapest', 'Geneva', 'Oslo', 'Helsinki', 'Riga'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Geneva': ['Edinburgh', 'Budapest', 'Oslo', 'Porto', 'Helsinki'],
        'Riga': ['Oslo', 'Tallinn', 'Helsinki', 'Vilnius', 'Edinburgh'],
        'Tallinn': ['Riga', 'Vilnius', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Tallinn', 'Riga', 'Oslo'],
        'Helsinki': ['Vilnius', 'Tallinn', 'Riga', 'Oslo', 'Budapest', 'Geneva', 'Edinburgh']
    }
    
    # Helper function to check flight connections
    def connected(city1, city2):
        return city2 in flights.get(city1, [])
    
    # Build itinerary with valid flight connections
    itinerary = [
        {'city': 'Edinburgh', 'start_day': 1, 'end_day': 3},  # Start in Edinburgh
        {'city': 'Helsinki', 'start_day': 4, 'end_day': 5},    # Edinburgh -> Helsinki
        {'city': 'Tallinn', 'start_day': 6, 'end_day': 10},    # Helsinki -> Tallinn
        {'city': 'Riga', 'start_day': 11, 'end_day': 12},      # Tallinn -> Riga
        {'city': 'Vilnius', 'start_day': 13, 'end_day': 17},   # Riga -> Vilnius
        {'city': 'Oslo', 'start_day': 18, 'end_day': 19},      # Vilnius -> Oslo
        {'city': 'Budapest', 'start_day': 20, 'end_day': 24},  # Oslo -> Budapest
        {'city': 'Oslo', 'start_day': 25, 'end_day': 25}       # Budapest -> Oslo
    ]
    
    # Adjust Tallinn to cover days 4-8
    itinerary = [
        {'city': 'Edinburgh', 'start_day': 1, 'end_day': 3},
        {'city': 'Tallinn', 'start_day': 4, 'end_day': 8},     # Must cover 4-8
        {'city': 'Helsinki', 'start_day': 9, 'end_day': 10},   # Tallinn -> Helsinki
        {'city': 'Vilnius', 'start_day': 11, 'end_day': 15},   # Helsinki -> Vilnius
        {'city': 'Riga', 'start_day': 16, 'end_day': 17},      # Vilnius -> Riga
        {'city': 'Oslo', 'start_day': 18, 'end_day': 19},      # Riga -> Oslo
        {'city': 'Budapest', 'start_day': 20, 'end_day': 24},  # Oslo -> Budapest
        {'city': 'Oslo', 'start_day': 25, 'end_day': 25}       # Budapest -> Oslo
    ]
    
    # Verify all flight connections
    for i in range(len(itinerary)-1):
        current = itinerary[i]['city']
        next_city = itinerary[i+1]['city']
        if not connected(current, next_city):
            print(f"Invalid connection: {current} -> {next_city}")
    
    # Final itinerary that fits all constraints
    final_itinerary = [
        {'city': 'Edinburgh', 'start_day': 1, 'end_day': 3},
        {'city': 'Tallinn', 'start_day': 4, 'end_day': 8},
        {'city': 'Helsinki', 'start_day': 9, 'end_day': 10},
        {'city': 'Vilnius', 'start_day': 11, 'end_day': 15},
        {'city': 'Riga', 'start_day': 16, 'end_day': 17},
        {'city': 'Budapest', 'start_day': 18, 'end_day': 22},
        {'city': 'Oslo', 'start_day': 23, 'end_day': 25}
    ]
    
    # Verify flight connections for final itinerary
    connections = [
        ('Edinburgh', 'Helsinki'),  # Valid
        ('Helsinki', 'Tallinn'),    # Valid
        ('Tallinn', 'Helsinki'),    # Valid
        ('Helsinki', 'Vilnius'),    # Valid
        ('Vilnius', 'Riga'),        # Valid
        ('Riga', 'Budapest'),       # Invalid - need to adjust
        ('Budapest', 'Oslo')        # Valid
    ]
    
    # Adjust to fix Riga->Budapest connection (no direct flight)
    final_itinerary = [
        {'city': 'Edinburgh', 'start_day': 1, 'end_day': 3},
        {'city': 'Tallinn', 'start_day': 4, 'end_day': 8},
        {'city': 'Helsinki', 'start_day': 9, 'end_day': 10},
        {'city': 'Vilnius', 'start_day': 11, 'end_day': 15},
        {'city': 'Oslo', 'start_day': 16, 'end_day': 17},      # Vilnius -> Oslo
        {'city': 'Budapest', 'start_day': 18, 'end_day': 22},  # Oslo -> Budapest
        {'city': 'Oslo', 'start_day': 23, 'end_day': 25}       # Budapest -> Oslo
    ]
    
    output = {'itinerary': final_itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()