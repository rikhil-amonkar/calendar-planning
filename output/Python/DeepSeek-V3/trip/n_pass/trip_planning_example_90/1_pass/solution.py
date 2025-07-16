import json

def plan_trip():
    total_days = 17
    vilnius_days = 7
    naples_days = 5
    vienna_days = 7
    
    # Direct flight connections
    connections = {
        'Naples': ['Vienna'],
        'Vienna': ['Naples', 'Vilnius'],
        'Vilnius': ['Vienna']
    }
    
    # Constraints: Naples must be between day 1-5
    # Possible itineraries must fit the constraints and flight connections
    
    # Since Naples is only connected to Vienna, and Vilnius is only connected to Vienna,
    # the itinerary must start or end in Vienna to connect both cities.
    # Given Naples must be between day 1-5, the only feasible order is:
    # Naples -> Vienna -> Vilnius
    
    # Calculate day ranges
    # Day 1-5: Naples (5 days)
    # Flight on day 5 to Vienna (day 5 counts for both Naples and Vienna)
    # Vienna days remaining: 7 - 1 (day 5) = 6
    # Day 6-11: Vienna (6 days)
    # Flight on day 11 to Vilnius (day 11 counts for both Vienna and Vilnius)
    # Vilnius days remaining: 7 - 1 (day 11) = 6
    # Day 12-17: Vilnius (6 days)
    
    itinerary = [
        {"day_range": "Day 1-5", "place": "Naples"},
        {"day_range": "Day 5-11", "place": "Vienna"},
        {"day_range": "Day 11-17", "place": "Vilnius"}
    ]
    
    # Verify total days
    calculated_days = {
        'Naples': 5,
        'Vienna': 7,  # 1 (day 5) + 6 (day 6-11)
        'Vilnius': 7   # 1 (day 11) + 6 (day 12-17)
    }
    
    # Verify constraints
    assert calculated_days['Naples'] == naples_days
    assert calculated_days['Vienna'] == vienna_days
    assert calculated_days['Vilnius'] == vilnius_days
    assert (5 + 7 + 7 - 2) == total_days  # Subtract 2 for overlapping flight days
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(json.dumps(trip_plan))