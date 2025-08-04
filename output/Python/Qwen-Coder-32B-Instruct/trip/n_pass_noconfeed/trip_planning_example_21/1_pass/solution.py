import json

def calculate_itinerary():
    # Input variables
    total_days = 10
    venice_stay = 6
    venice_workshop_start = 5
    venice_workshop_end = 10
    mykonos_stay = 2
    vienna_stay = 4
    
    # Initialize itinerary list
    itinerary = []
    
    # Start with Vienna since it's the only starting point that allows reaching Venice in time for the workshop
    current_day = 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + vienna_stay - 1}", "place": "Vienna"})
    current_day += vienna_stay
    
    # Move to Venice for the workshop
    itinerary.append({"day_range": f"Day {current_day}-{current_day + venice_stay - 1}", "place": "Venice"})
    current_day += venice_stay
    
    # Adjust the last entry to reflect the workshop constraint
    workshop_start_day = venice_workshop_start
    workshop_end_day = min(venice_workshop_end, current_day - 1)
    non_workshop_days_in_venice = workshop_start_day - (current_day - venice_stay)
    
    if non_workshop_days_in_venice > 0:
        itinerary[-1]["day_range"] = f"Day {current_day - venice_stay}-{current_day - venice_stay + non_workshop_days_in_venice - 1}"
        current_day = current_day - venice_stay + non_workshop_days_in_venice
    
    # Add the workshop days
    if workshop_end_day >= workshop_start_day:
        itinerary.append({"day_range": f"Day {workshop_start_day}-{workshop_end_day}", "place": "Venice (Workshop)"})
        current_day = workshop_end_day + 1
    
    # If there are remaining days, allocate them to Mykonos
    if current_day <= total_days:
        mykonos_end_day = min(current_day + mykonos_stay - 1, total_days)
        itinerary.append({"day_range": f"Day {current_day}-{mykonos_end_day}", "place": "Mykonos"})
        current_day = mykonos_end_day + 1
    
    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())