# Define constraints for different cities
constraints = {
    'New York': (1, (9, 18)),  # Example: min day is 1, start time is 9 AM, end time is 6 PM
    'Los Angeles': (2, (10, 17)),
    'Chicago': (3, (8, 19))
}

# Example city
city = 'New York'

# Check if the city exists in the constraints dictionary
if city in constraints:
    min_day, (start, end) = constraints[city]
    print(f"Constraints for {city}: Min day = {min_day}, Start time = {start}, End time = {end}")
else:
    print(f"No constraints found for {city}")