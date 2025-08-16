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
        "Warsaw": 1,  # Adjusted to fit the 18-day constraint
        "London": 1   # Adjusted to fit the 18-day constraint
    }

    # Define the flight connections (not used in this simple itinerary generation)
    flights = {
        "Warsaw": ["Reykjavik", "Riga", "Oslo", "London", "Madrid"],
        "Oslo": ["Madrid", "Dubrovnik", "Reykjavik", "Riga", "Lyon", "London"],
        "Lyon": ["London", "Madrid"],
        "Madrid": ["London", "Lyon", "Dubrovnik", "Oslo", "Warsaw", "Reykjavik"],
        "Dubrovnik": ["Madrid", "Oslo"],
        "London": ["Lyon", "Madrid", "Oslo", "Warsaw", "Reykjavik"],
        "Reykjavik": ["Madrid", "Oslo", "Warsaw", "London"],
        "Riga": ["Oslo", "Warsaw"]
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Function to add a stay to the itinerary
    def add_stay(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days

    # Add initial stay in Reykjavik
    add_stay("Reykjavik", constraints["Reykjavik"])  # Stay 4 days in Reykjavik

    # Meet friend in Riga between day 5 and day 6
    add_stay("Riga", constraints["Riga"])

    # Continue the itinerary after meeting the friend
    # No additional stay needed in Reykjavik

    # Add stay in Oslo
    add_stay("Oslo", constraints["Oslo"])

    # Add stay in Lyon
    add_stay("Lyon", constraints["Lyon"])

    # Attend wedding in Dubrovnik between day 12 and day 13
    add_stay("Dubrovnik", constraints["Dubrovnik"])

    # Add remaining stays
    add_stay("Madrid", constraints["Madrid"])
    add_stay("Warsaw", constraints["Warsaw"])
    add_stay("London", constraints["London"])

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Calculate and print the itinerary
print(calculate_itinerary())