import json

def main():
    # Define cities and their required durations
    cities = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5
    }

    # Define direct flight connections as a graph
    flight_graph = {
        "Stockholm": {"Oslo", "Munich", "Hamburg", "Istanbul", "Santorini"},
        "Hamburg": {"Stockholm", "Munich", "Istanbul", "Frankfurt", "Oslo"},
        "Florence": {"Frankfurt", "Munich"},
        "Istanbul": {"Krakow", "Frankfurt", "Oslo", "Vilnius", "Munich", "Hamburg", "Stockholm"},
        "Oslo": {"Stockholm", "Istanbul", "Krakow", "Frankfurt", "Munich", "Hamburg", "Vilnius"},
        "Vilnius": {"Krakow", "Frankfurt", "Istanbul"},
        "Santorini": {"Stockholm", "Oslo"},
        "Munich": {"Stockholm", "Hamburg", "Istanbul", "Frankfurt", "Krakow", "Florence"},
        "Frankfurt": {"Krakow", "Istanbul", "Oslo", "Munich", "Hamburg", "Florence", "Stockholm"},
        "Krakow": {"Frankfurt", "Istanbul", "Vilnius", "Munich", "Oslo", "Stockholm"}
    }

    # Initialize itinerary
    itinerary = []
    current_day = 1

    # Add Florence (2 days)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+1}", "place": "Florence"})
    current_day += 2

    # Add Munich (5 days)
    if "Munich" in flight_graph["Florence"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+4}", "place": "Munich"})
        current_day += 5
    else:
        raise ValueError("No direct flight from Florence to Munich")

    # Add Frankfurt (4 days)
    if "Frankfurt" in flight_graph["Munich"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+3}", "place": "Frankfurt"})
        current_day += 4
    else:
        raise ValueError("No direct flight from Munich to Frankfurt")

    # Add Krakow (5 days with workshop)
    if "Krakow" in flight_graph["Frankfurt"]:
        start_day = current_day
        end_day = current_day + 4
        # Ensure workshop is between day 5-9
        if start_day <= 9 and end_day >= 5:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Krakow"})
            current_day = end_day + 1
        else:
            raise ValueError("Krakow stay does not overlap with workshop days")
    else:
        raise ValueError("No direct flight from Frankfurt to Krakow")

    # Add Munich (5 days)
    if "Munich" in flight_graph["Krakow"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+4}", "place": "Munich"})
        current_day += 5
    else:
        raise ValueError("No direct flight from Krakow to Munich")

    # Add Hamburg (5 days)
    if "Hamburg" in flight_graph["Munich"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+4}", "place": "Hamburg"})
        current_day += 5
    else:
        raise ValueError("No direct flight from Munich to Hamburg")

    # Add Oslo (5 days)
    if "Oslo" in flight_graph["Hamburg"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+4}", "place": "Oslo"})
        current_day += 5
    else:
        raise ValueError("No direct flight from Hamburg to Oslo")

    # Add Vilnius (5 days)
    if "Vilnius" in flight_graph["Oslo"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+4}", "place": "Vilnius"})
        current_day += 5
    else:
        raise ValueError("No direct flight from Oslo to Vilnius")

    # Add Istanbul (5 days for the show)
    if "Istanbul" in flight_graph["Vilnius"]:
        start_day = current_day
        end_day = current_day + 4
        # Ensure show is from day 25-29
        if start_day == 25 and end_day == 29:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Istanbul"})
            current_day = end_day + 1
        else:
            raise ValueError("Istanbul stay does not align with the show days")
    else:
        raise ValueError("No direct flight from Vilnius to Istanbul")

    # Add Stockholm (3 days)
    if "Stockholm" in flight_graph["Istanbul"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+2}", "place": "Stockholm"})
        current_day += 3
    else:
        raise ValueError("No direct flight from Istanbul to Stockholm")

    # Add Santorini (2 days)
    if "Santorini" in flight_graph["Stockholm"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+1}", "place": "Santorini"})
        current_day += 2
    else:
        raise ValueError("No direct flight from Stockholm to Santorini")

    # Verify total days
    if current_day - 1 != 32:
        raise ValueError(f"Total days ({current_day - 1}) do not match required 32 days")

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()