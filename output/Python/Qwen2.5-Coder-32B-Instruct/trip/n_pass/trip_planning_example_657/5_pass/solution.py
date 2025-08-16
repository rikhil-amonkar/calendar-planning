import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Frankfurt": (4, [13, 16]),
        "Manchester": (4, []),
        "Valencia": (4, []),
        "Naples": (4, []),
        "Oslo": (3, []),
        "Vilnius": (2, [12, 13])
    }
    
    # Define the direct flight connections
    flights = {
        "Valencia": ["Frankfurt"],
        "Manchester": ["Frankfurt", "Naples", "Oslo"],
        "Naples": ["Manchester", "Frankfurt", "Oslo"],
        "Oslo": ["Naples", "Manchester", "Frankfurt", "Vilnius"],
        "Vilnius": ["Oslo", "Frankfurt"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Function to add a stay to the itinerary
    def add_stay(city, days):
        nonlocal current_day
        end_day = current_day + days - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Function to check if a day is forbidden for travel
    def is_forbidden(city, day):
        return day in constraints[city][1]
    
    # Start planning the itinerary
    # Start in Frankfurt for the show
    add_stay("Frankfurt", 5)  # Days 1-5
    
    # Attend the wedding in Vilnius on Day 6 and 7
    add_stay("Vilnius", 2)  # Days 6-7
    
    # Continue the show in Frankfurt
    add_stay("Frankfurt", 3)  # Days 8-10
    
    # Go to Manchester from Frankfurt
    # Ensure we do not travel on forbidden days (Day 12, 13)
    while is_forbidden("Manchester", current_day):
        current_day += 1
    add_stay("Manchester", 3)  # Days 11-13
    
    # Go to Valencia from Manchester
    # Ensure we do not travel on forbidden days
    while is_forbidden("Valencia", current_day):
        current_day += 1
    add_stay("Valencia", 3)  # Days 14-16
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())