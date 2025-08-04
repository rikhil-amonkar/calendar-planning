# Define constraints for different cities
# Each tuple now contains: (minimum starting day, (start time, end time), total number of days)
constraints = {
    'New York': (1, (9, 18), 26),  # Example: min day is 1, start time is 9 AM, end time is 6 PM, total days is 26
    'Los Angeles': (2, (10, 17), 26),
    'Chicago': (3, (8, 19), 26)
}

# Example city
city = 'New York'

# Check if the city exists in the constraints dictionary
if city in constraints:
    min_day, (start, end), total_days = constraints[city]
    print(f"Constraints for {city}: Min day = {min_day}, Start time = {start}, End time = {end}, Total days = {total_days}")
    
    # Verify if the total days constraint is satisfied
    if total_days == 26:
        print("The itinerary covers exactly 26 days.")
    else:
        print("The itinerary does not cover exactly 26 days.")
else:
    print(f"No constraints found for {city}")