import json

def calculate_itinerary():
    # Define the constraints with adjusted days to sum up to 18
    constraints = {
        "Venice": 5,
        "Frankfurt": 3,
        "Salzburg": 3,
        "Florence": 3,
        "Barcelona": 2,
        "Stuttgart": 1,
        "Stockholm": 1
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Iterate through each place and its corresponding days
    for place, days in constraints.items():
        end_day = current_day + days - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": place})
        current_day += days
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())