import json

def calculate_itinerary():
    # Input constraints
    total_days = 12
    days_in_vilnius = 4
    days_in_munich = 3
    days_in_mykonos = 7
    
    # Direct flights: Vilnius -> Munich, Munich -> Mykonos
    
    # Initialize itinerary list
    itinerary = []
    
    # Start in Vilnius
    start_day = 1
    end_day = start_day + days_in_vilnius - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Vilnius"})
    
    # Move to Munich
    start_day = end_day
    end_day = start_day + days_in_munich - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Munich"})
    
    # Move to Mykonos
    start_day = end_day
    end_day = start_day + days_in_mykonos - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Mykonos"})
    
    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())