import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3,
        "meet_friend_riga": (4, 5),
        "wedding_dubrovnik": (7, 8)
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Function to add a stay to the itinerary
    def add_stay(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days

    # Function to add travel days to the itinerary
    def add_travel(days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": "Travel"})
        current_day += days

    # Start in Reykjavik
    add_stay("Reykjavik", constraints["Reykjavik"])

    # Adjust the current day to meet the friend in Riga on the required day
    if current_day < constraints["meet_friend_riga"][0]:
        # Add travel days to reach the required day
        travel_days = constraints["meet_friend_riga"][0] - current_day
        add_travel(travel_days)

    # Go to Riga to meet friend
    add_stay("Riga", constraints["Riga"])

    # Adjust the current day to attend the wedding in Dubrovnik on the required day
    if current_day < constraints["wedding_dubrovnik"][0]:
        # Add travel days to reach the required day
        travel_days = constraints["wedding_dubrovnik"][0] - current_day
        add_travel(travel_days)

    # Go to Dubrovnik for wedding
    add_stay("Dubrovnik", constraints["Dubrovnik"])

    # Continue the itinerary
    add_travel(1)  # Travel day from Dubrovnik to Oslo
    add_stay("Oslo", constraints["Oslo"])
    add_travel(1)  # Travel day from Oslo to Lyon
    add_stay("Lyon", constraints["Lyon"])
    add_travel(1)  # Travel day from Lyon to Warsaw
    add_stay("Warsaw", constraints["Warsaw"])
    add_travel(1)  # Travel day from Warsaw to London
    add_stay("London", constraints["London"])
    add_travel(1)  # Travel day from London to Madrid
    add_stay("Madrid", constraints["Madrid"])

    # Ensure all days are accounted for
    if current_day != 19:
        raise ValueError("Itinerary does not cover exactly 18 days")

    return itinerary

# Calculate and print the itinerary as JSON
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))