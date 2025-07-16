import json

def compute_itinerary():
    # Input parameters
    total_days = 15
    cities = {
        'Stuttgart': {'total_days': 5, 'workshop': (11, 15)},
        'Manchester': {'total_days': 7, 'wedding': (1, 7)},
        'Madrid': {'total_days': 4},
        'Vienna': {'total_days': 2}
    }
    
    direct_flights = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Fixed events first
    # Wedding in Manchester must be days 1-7
    itinerary.append({"day_range": "Day 1-7", "place": "Manchester"})
    
    # Workshop in Stuttgart must be days 11-15
    # So we have days 8-10 (3 days) before Stuttgart
    
    # Solution: 
    # 1. Go to Madrid first (days 8-11) - but this conflicts with Stuttgart workshop
    # 2. Go to Vienna first (days 8-9), then Madrid (days 10-13) - but this goes beyond Stuttgart workshop
    # 3. Alternative approach: Adjust Madrid to be after Stuttgart
    
    # Best solution: Visit Madrid after Stuttgart, but we need to check flight connections
    # Manchester (1-7) -> Vienna (8-9) -> Stuttgart (11-15)
    # Then Madrid would have to be after day 15, but we only have 15 days
    
    # Final decision: Since we can't satisfy all city day requirements in 15 days,
    # we'll prioritize the fixed events and maximize days in other cities
    
    # Revised plan:
    # 1-7: Manchester (wedding)
    # 8-11: Madrid (4 days)
    # 12-15: Stuttgart (workshop - but this only gives 4 days instead of required 5)
    # This still doesn't work
    
    # Only possible solution is to skip Vienna to accommodate both Madrid and Stuttgart
    itinerary.append({"day_range": "Day 8-11", "place": "Madrid"})  # 4 days
    itinerary.append({"day_range": "Day 12-15", "place": "Stuttgart"})  # 4 days (1 short)
    
    # This means:
    # - Manchester: 7/7 days (perfect)
    # - Madrid: 4/4 days (perfect)
    # - Stuttgart: 4/5 days (1 day short)
    # - Vienna: skipped
    
    # This is the closest we can get while satisfying most constraints
    
    final_itinerary = {
        "itinerary": itinerary
    }
    
    return final_itinerary

# Output the result as JSON
print(json.dumps(compute_itinerary()))