import json

def calculate_itinerary():
    # Define the constraints
    total_days = 20
    days_in_hamburg = 7
    days_in_munich = 6
    days_in_manchester = 2
    days_in_lyon = 2
    days_in_split = 7
    
    # Fixed events
    manchester_visit_days = (19, 20)
    lyon_show_days = (13, 14)
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Split for 7 days (Day 1-7)
    itinerary.append({"day_range": f"Day 1-{days_in_split}", "place": "Split"})
    current_day = days_in_split + 1
    
    # Move to Munich for 6 days (Day 8-13)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_munich - 1}", "place": "Munich"})
    current_day += days_in_munich
    
    # Attend the show in Lyon (Day 13-14)
    itinerary.append({"day_range": f"Day {lyon_show_days[0]}-{lyon_show_days[1]}", "place": "Lyon"})
    current_day = lyon_show_days[1] + 1
    
    # Move to Manchester for 2 days (Day 16-17)
    if current_day < manchester_visit_days[0]:
        # Fill the gap with Munich if necessary
        itinerary.append({"day_range": f"Day {current_day}-{manchester_visit_days[0] - 1}", "place": "Munich"})
        current_day = manchester_visit_days[0]
    
    # Visit relatives in Manchester (Day 19-20)
    itinerary.append({"day_range": f"Day {manchester_visit_days[0]}-{manchester_visit_days[1]}", "place": "Manchester"})
    current_day = manchester_visit_days[1] + 1
    
    # Fill the remaining days with Hamburg
    if current_day <= total_days:
        itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Hamburg"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as JSON
print(json.dumps({"itinerary": itinerary}, indent=4))