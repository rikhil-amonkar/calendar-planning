import json

def calculate_itinerary():
    # Input constraints
    total_days = 12
    split_days = 2
    helsinki_days = 2
    reykjavik_days = 3
    reykjavik_wedding_days = range(10, 13)
    vilnius_days = 3
    vilnius_relative_days = range(7, 10)
    geneva_days = 6
    
    # Direct flight connections
    connections = {
        'Split': ['Helsinki', 'Geneva', 'Vilnius'],
        'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
        'Geneva': ['Split', 'Helsinki'],
        'Reykjavik': ['Helsinki'],
        'Vilnius': ['Split', 'Helsinki']
    }
    
    # Initialize itinerary
    itinerary = []
    current_day = 1
    current_city = None
    
    # Place Vilnius first to satisfy relative visit
    itinerary.append({"day_range": f"Day {current_day}-{current_day + vilnius_days - 1}", "place": "Vilnius"})
    current_day += vilnius_days
    current_city = "Vilnius"
    
    # Move to Helsinki after Vilnius
    itinerary.append({"day_range": f"Day {current_day}-{current_day + helsinki_days - 1}", "place": "Helsinki"})
    current_day += helsinki_days
    current_city = "Helsinki"
    
    # Move to Geneva after Helsinki
    itinerary.append({"day_range": f"Day {current_day}-{current_day + geneva_days - 1}", "place": "Geneva"})
    current_day += geneva_days
    current_city = "Geneva"
    
    # Move to Split after Geneva
    itinerary.append({"day_range": f"Day {current_day}-{current_day + split_days - 1}", "place": "Split"})
    current_day += split_days
    current_city = "Split"
    
    # Move to Reykjavik for wedding
    itinerary.append({"day_range": f"Day {current_day}-{current_day + reykjavik_days - 1}", "place": "Reykjavik"})
    current_day += reykjavik_days
    current_city = "Reykjavik"
    
    return itinerary

# Calculate and output the itinerary
itinerary = calculate_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output))