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

    # Define the possible flights
    flights = [
        ("Warsaw", "Reykjavik"), ("Oslo", "Madrid"), ("Warsaw", "Riga"),
        ("Lyon", "London"), ("Madrid", "London"), ("Warsaw", "London"),
        ("Reykjavik", "Madrid"), ("Warsaw", "Oslo"), ("Oslo", "Dubrovnik"),
        ("Oslo", "Reykjavik"), ("Riga", "Oslo"), ("Oslo", "Lyon"),
        ("Oslo", "London"), ("London", "Reykjavik"), ("Warsaw", "Madrid"),
        ("Madrid", "Lyon"), ("Dubrovnik", "Madrid")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Function to add a stay to the itinerary
    def add_stay(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days

    # Start in Reykjavik
    add_stay("Reykjavik", constraints["Reykjavik"])

    # Go to Riga to meet friend
    if current_day == constraints["meet_friend_riga"][0]:
        add_stay("Riga", constraints["Riga"])
    else:
        raise ValueError("Cannot meet friend in Riga on the required day")

    # Go to Oslo
    add_stay("Oslo", constraints["Oslo"])

    # Go to Dubrovnik for wedding
    if current_day == constraints["wedding_dubrovnik"][0]:
        add_stay("Dubrovnik", constraints["Dubrovnik"])
    else:
        raise ValueError("Cannot attend wedding in Dubrovnik on the required day")

    # Go to Lyon
    add_stay("Lyon", constraints["Lyon"])

    # Go to Warsaw
    add_stay("Warsaw", constraints["Warsaw"])

    # Go to London
    add_stay("London", constraints["London"])

    # Go to Madrid
    add_stay("Madrid", constraints["Madrid"])

    # Ensure all days are accounted for
    if current_day != 19:
        raise ValueError("Itinerary does not cover exactly 18 days")

    return itinerary

# Calculate and print the itinerary as JSON
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))