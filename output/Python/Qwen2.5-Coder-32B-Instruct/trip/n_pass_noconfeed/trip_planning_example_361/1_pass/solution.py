import json

def calculate_itinerary():
    # Define the constraints
    total_days = 15
    days_in_paris = 6
    days_in_madrid = 7
    days_in_bucharest = 2
    days_in_seville = 3
    
    # Fixed schedule
    madrid_show_start = 1
    madrid_show_end = 7
    bucharest_visit_start = 14
    bucharest_visit_end = 15
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Madrid for the show
    itinerary.append({"day_range": f"Day {madrid_show_start}-{madrid_show_end}", "place": "Madrid"})
    
    # Move to Seville after the show
    seville_start = madrid_show_end + 1
    seville_end = seville_start + days_in_seville - 1
    itinerary.append({"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"})
    
    # Move to Paris from Seville
    paris_start = seville_end + 1
    paris_end = paris_start + days_in_paris - 1
    itinerary.append({"day_range": f"Day {paris_start}-{paris_end}", "place": "Paris"})
    
    # Move to Bucharest from Paris
    bucharest_start = paris_end + 1
    bucharest_end = bucharest_start + days_in_bucharest - 1
    itinerary.append({"day_range": f"Day {bucharest_start}-{bucharest_end}", "place": "Bucharest"})
    
    # Adjust the last part of the itinerary to ensure it fits within the total days and includes the fixed Bucharest visit
    if bucharest_end < bucharest_visit_start:
        # Add remaining days in Bucharest
        remaining_days = total_days - bucharest_end
        if remaining_days > 0:
            itinerary.append({"day_range": f"Day {bucharest_end+1}-{total_days}", "place": "Bucharest"})
    else:
        # Ensure the Bucharest visit is included
        itinerary[-1] = {"day_range": f"Day {bucharest_visit_start}-{bucharest_visit_end}", "place": "Bucharest"}
    
    return itinerary

# Calculate and output the itinerary as JSON
itinerary = calculate_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output))