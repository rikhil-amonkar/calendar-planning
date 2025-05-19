import json

def plan_trip():
    # Define the total trip duration and starting day
    total_days = 25
    itinerary = []

    # Define stay durations and constraints
    stays = {
        "Valencia": {"duration": 2, "meet_days": (3, 4)},
        "Oslo": {"duration": 3, "meet_days": (13, 15)},
        "Lyon": {"duration": 4},
        "Prague": {"duration": 3},
        "Paris": {"duration": 4},
        "Nice": {"duration": 4},
        "Seville": {"duration": 5, "event_days": (5, 9)},
        "Tallinn": {"duration": 2},
        "Mykonos": {"duration": 5, "wedding_days": (21, 25)},
        "Lisbon": {"duration": 2}
    }
    
    # Flight connections
    flights = {
        "Lisbon": ["Paris", "Seville"],
        "Paris": ["Lisbon", "Oslo", "Nice", "Valencia", "Lyon"],
        "Lyon": ["Nice", "Prague", "Valencia"],
        "Tallinn": ["Oslo"],
        "Prague": ["Lyon", "Lisbon", "Oslo", "Paris"],
        "Oslo": ["Tallinn", "Nice", "Paris", "Lyon"],
        "Valencia": ["Paris", "Lisbon", "Lyon", "Seville"],
        "Nice": ["Paris", "Lyon", "Mykonos"],
        "Seville": ["Lisbon", "Paris"],
        "Mykonos": []
    }

    days = 1
    visited_cities = []
    
    # Start with Valencia
    visited_cities.append("Valencia")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Valencia']['duration'] - 1}", "place": "Valencia"})
    days += stays["Valencia"]["duration"]
    
    # Meet friends in Valencia
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Valencia", "to": "Paris"})
    visited_cities.append("Paris")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Paris']['duration'] - 1}", "place": "Paris"})
    days += stays["Paris"]["duration"]

    # Travel to Lyon next
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Paris", "to": "Lyon"})
    visited_cities.append("Lyon")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Lyon']['duration'] - 1}", "place": "Lyon"})
    days += stays["Lyon"]["duration"]

    # Travel to Nice
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Lyon", "to": "Nice"})
    visited_cities.append("Nice")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Nice']['duration'] - 1}", "place": "Nice"})
    days += stays["Nice"]["duration"]

    # Travel to Seville
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Nice", "to": "Seville"})
    visited_cities.append("Seville")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Seville']['duration'] - 1}", "place": "Seville"})
    days += stays["Seville"]["duration"]

    # Now to Oslo
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Seville", "to": "Oslo"})
    visited_cities.append("Oslo")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Oslo']['duration'] - 1}", "place": "Oslo"})
    days += stays["Oslo"]["duration"]

    # Travel to Prague
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Oslo", "to": "Prague"})
    visited_cities.append("Prague")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Prague']['duration'] - 1}", "place": "Prague"})
    days += stays["Prague"]["duration"]

    # Travel to Tallinn
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Prague", "to": "Tallinn"})
    visited_cities.append("Tallinn")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Tallinn']['duration'] - 1}", "place": "Tallinn"})
    days += stays["Tallinn"]["duration"]

    # Travel to Lisbon
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Tallinn", "to": "Lisbon"})
    visited_cities.append("Lisbon")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Lisbon']['duration'] - 1}", "place": "Lisbon"})
    days += stays["Lisbon"]["duration"]

    # Finally travel to Mykonos
    itinerary.append({"flying": f"Day {days}-{days}", "from": "Lisbon", "to": "Mykonos"})
    visited_cities.append("Mykonos")
    itinerary.append({"day_range": f"Day {days}-{days + stays['Mykonos']['duration'] - 1}", "place": "Mykonos"})
    days += stays["Mykonos"]["duration"]

    # Output the itinerary as JSON
    return json.dumps(itinerary, indent=4)

# Run the trip planner
if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)