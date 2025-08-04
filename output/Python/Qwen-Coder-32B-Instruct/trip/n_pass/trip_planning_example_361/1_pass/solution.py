import json

def calculate_itinerary():
    # Define the constraints
    total_days = 15
    days_in_paris = 6
    days_in_madrid = 7
    days_in_bucharest = 2
    days_in_seville = 3
    madrid_show_start = 1
    madrid_show_end = 7
    bucharest_visit_start = 14
    bucharest_visit_end = 15
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Madrid for the show
    itinerary.append({"day_range": f"Day {madrid_show_start}-{madrid_show_end}", "place": "Madrid"})
    
    # Move to Seville after the show
    current_day = madrid_show_end + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_seville - 1}", "place": "Seville"})
    current_day += days_in_seville
    
    # Move to Paris
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_paris - 1}", "place": "Paris"})
    current_day += days_in_paris
    
    # Move to Bucharest for the visit
    itinerary.append({"day_range": f"Day {bucharest_visit_start}-{bucharest_visit_end}", "place": "Bucharest"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())