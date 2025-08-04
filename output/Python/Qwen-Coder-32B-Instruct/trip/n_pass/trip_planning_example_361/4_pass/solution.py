import json

def calculate_itinerary():
    # Define the constraints
    total_days = 15
    days_in_paris = 3
    days_in_madrid = 7
    days_in_bucharest = 2
    days_in_seville = 3
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Madrid for the show
    madrid_show_start = 1
    madrid_show_end = madrid_show_start + days_in_madrid - 1
    itinerary.append({"day_range": f"Day {madrid_show_start}-{madrid_show_end}", "place": "Madrid"})
    
    # Move to Seville after the show
    seville_start = madrid_show_end + 1
    seville_end = seville_start + days_in_seville - 1
    itinerary.append({"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"})
    
    # Move to Paris
    paris_start = seville_end + 1
    paris_end = paris_start + days_in_paris - 1
    itinerary.append({"day_range": f"Day {paris_start}-{paris_end}", "place": "Paris"})
    
    # Move to Bucharest for the visit
    bucharest_start = paris_end + 1
    bucharest_end = bucharest_start + days_in_bucharest - 1
    itinerary.append({"day_range": f"Day {bucharest_start}-{bucharest_end}", "place": "Bucharest"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())