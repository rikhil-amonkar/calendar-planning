import json

def calculate_itinerary():
    # Input variables
    total_days = 12
    vilnius_days = 4
    munich_days = 3
    mykonos_days = 5  # Adjusted to fit 12 days total
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Vilnius
    current_day = 1
    
    # Add Vilnius to itinerary
    itinerary.append({"day_range": f"Day {current_day}-{current_day + vilnius_days - 1}", "place": "Vilnius"})
    current_day += vilnius_days
    
    # Fly from Vilnius to Munich
    itinerary.append({"day_range": f"Day {current_day}-{current_day + munich_days - 1}", "place": "Munich"})
    current_day += munich_days
    
    # Fly from Munich to Mykonos
    itinerary.append({"day_range": f"Day {current_day}-{current_day + mykonos_days - 1}", "place": "Mykonos"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())