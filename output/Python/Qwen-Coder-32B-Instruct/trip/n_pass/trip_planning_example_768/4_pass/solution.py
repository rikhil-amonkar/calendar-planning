import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4
    }
    
    # Define the mandatory days in Nice
    mandatory_days_nice = {14, 16}
    
    # Define the friend meeting window in Oslo
    friend_meeting_window = range(10, 15)
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None
    
    # Place Mykonos first since it has a fixed duration
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Mykonos'] - 1}", "place": "Mykonos"})
    current_day += constraints['Mykonos']
    current_city = "Mykonos"
    
    # Move to London after Mykonos
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['London'] - 1}", "place": "London"})
    current_day += constraints['London']
    current_city = "London"
    
    # Move to Copenhagen after London
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Copenhagen'] - 1}", "place": "Copenhagen"})
    current_day += constraints['Copenhagen']
    current_city = "Copenhagen"
    
    # Ensure Nice is visited on days 14 and 16
    # Nice needs to be visited for 3 days, so it should start on day 13
    nice_start_day = 13
    if nice_start_day < current_day:
        raise ValueError("Cannot fit Nice into the itinerary with the given constraints.")
    if nice_start_day > current_day:
        # Add a transit day if needed
        itinerary.append({"day_range": f"Day {current_day}-{nice_start_day - 1}", "place": current_city})
        current_day = nice_start_day
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Nice'] - 1}", "place": "Nice"})
    current_day += constraints['Nice']
    current_city = "Nice"
    
    # Move to Oslo after Nice, ensuring we are in Oslo during the friend meeting window
    # Adjust the start day of Oslo to fit the friend meeting window
    oslo_start_day = max(current_day, min(friend_meeting_window) - constraints['Oslo'] + 1)
    if oslo_start_day > current_day:
        # Add a transit day if needed
        itinerary.append({"day_range": f"Day {current_day}-{oslo_start_day - 1}", "place": current_city})
        current_day = oslo_start_day
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Oslo'] - 1}", "place": "Oslo"})
    current_day += constraints['Oslo']
    current_city = "Oslo"
    
    # Fill remaining days if needed
    if current_day < 16:
        itinerary.append({"day_range": f"Day {current_day}-Day 16", "place": current_city})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
try:
    print(calculate_itinerary())
except ValueError as e:
    print(e)