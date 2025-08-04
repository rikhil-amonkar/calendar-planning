import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Valencia": (2, 3, 4),
        "Oslo": (3, 13, 15),
        "Lyon": 4,
        "Prague": 3,
        "Paris": 4,
        "Nice": 4,
        "Seville": (5, 5, 9, 9),
        "Tallinn": 2,
        "Mykonos": (5, 21, 25, 25),
        "Lisbon": 2
    }
    
    # Define the direct flights
    direct_flights = {
        "Lisbon": ["Paris", "Seville", "Nice", "Oslo", "Lyon"],
        "Paris": ["Lisbon", "Nice", "Oslo", "Lyon", "Valencia", "Tallinn", "Seville"],
        "Nice": ["Lisbon", "Paris", "Oslo", "Mykonos", "Lyon"],
        "Oslo": ["Lisbon", "Paris", "Nice", "Lyon", "Tallinn", "Prague"],
        "Lyon": ["Nice", "Paris", "Oslo", "Prague", "Valencia", "Seville"],
        "Valencia": ["Paris", "Lisbon", "Lyon", "Seville", "Prague"],
        "Tallinn": ["Oslo", "Paris", "Prague"],
        "Mykonos": ["Nice"],
        "Seville": ["Lisbon", "Paris", "Lyon", "Valencia"],
        "Prague": ["Oslo", "Paris", "Lyon", "Valencia", "Tallinn"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to add a stay to the itinerary
    def add_stay(city, start_day, end_day):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Start with a city that has direct flights to many others
    current_city = "Paris"
    
    # Add stays according to constraints
    add_stay("Paris", 1, 4)  # Stay in Paris until day 4 to meet friends in Valencia
    
    # Move to Valencia
    add_stay("Valencia", 4, 5)  # Meet friends in Valencia on day 4 and 5
    
    # Move to Seville for the show
    add_stay("Seville", 5, 9)  # Attend the show in Seville from day 5 to day 9
    
    # Continue staying in Seville
    add_stay("Seville", 10, 12)  # Stay in Seville until day 12
    
    # Move to Lisbon
    add_stay("Lisbon", 13, 14)  # Stay in Lisbon for 2 days
    
    # Move to Tallinn
    add_stay("Tallinn", 15, 16)  # Stay in Tallinn for 2 days
    
    # Move to Oslo
    add_stay("Oslo", 17, 19)  # Stay in Oslo until day 19
    
    # Continue staying in Oslo to meet friend
    add_stay("Oslo", 20, 22)  # Meet friend in Oslo from day 20 to day 22
    
    # Move to Prague
    add_stay("Prague", 23, 25)  # Stay in Prague until day 25
    
    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())