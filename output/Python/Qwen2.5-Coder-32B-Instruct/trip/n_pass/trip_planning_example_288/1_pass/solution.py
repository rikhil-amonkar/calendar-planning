import json

def calculate_itinerary():
    # Input constraints
    total_days = 15
    stuttgart_days = 5
    stuttgart_workshop_days = range(10, 15)  # Day 11 to Day 15 (0-indexed)
    manchester_days = 7
    manchester_wedding_days = range(0, 7)  # Day 1 to Day 7 (0-indexed)
    madrid_days = 4
    vienna_days = 2
    
    # Direct flight connections
    connections = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester'],
        'Stuttgart': ['Vienna', 'Manchester']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Manchester stay (Day 1-7)
    itinerary.append({"day_range": f"Day 1-{manchester_days}", "place": "Manchester"})
    
    # Vienna stay (Day 8-9)
    itinerary.append({"day_range": f"Day {manchester_days + 1}-{manchester_days + vienna_days}", "place": "Vienna"})
    
    # Stuttgart stay (Day 10-14)
    itinerary.append({"day_range": f"Day {manchester_days + vienna_days + 1}-{manchester_days + vienna_days + stuttgart_days}", "place": "Stuttgart"})
    
    # Madrid stay (Day 15)
    itinerary.append({"day_range": f"Day {total_days - madrid_days + 1}-{total_days}", "place": "Madrid"})
    
    return itinerary

# Calculate and output the itinerary as JSON
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))