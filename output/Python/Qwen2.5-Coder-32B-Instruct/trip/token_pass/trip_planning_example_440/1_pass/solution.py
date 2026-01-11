import json

def calculate_itinerary():
    # Define the constraints
    days = 12
    split_days = 2
    helsinki_days = 2
    reykjavik_days = 3
    vilnius_days = 3
    geneva_days = 6
    
    # Fixed days for Reykjavik and Vilnius
    reykjavik_start = 10
    reykjavik_end = reykjavik_start + reykjavik_days - 1
    
    vilnius_start = 7
    vilnius_end = vilnius_start + vilnius_days - 1
    
    # Initialize the itinerary
    itinerary = []
    
    # Add Vilnius days
    itinerary.append({"day_range": f"Day {vilnius_start}-{vilnius_end}", "place": "Vilnius"})
    
    # Add Helsinki days around Vilnius
    helsinki_start = 5
    helsinki_end = helsinki_start + helsinki_days - 1
    itinerary.append({"day_range": f"Day {helsinki_start}-{helsinki_end}", "place": "Helsinki"})
    
    # Add Split days around Helsinki and Vilnius
    split_start = 3
    split_end = split_start + split_days - 1
    itinerary.append({"day_range": f"Day {split_start}-{split_end}", "place": "Split"})
    
    # Add Reykjavik days
    itinerary.append({"day_range": f"Day {reykjavik_start}-{reykjavik_end}", "place": "Reykjavik"})
    
    # Add Geneva days
    geneva_start = 1
    geneva_end = geneva_start + geneva_days - 1
    itinerary.append({"day_range": f"Day {geneva_start}-{geneva_end}", "place": "Geneva"})
    
    # Sort the itinerary by day_range start
    itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split()[1]))
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
itinerary_json = calculate_itinerary()
print(json.dumps(itinerary_json, indent=4))