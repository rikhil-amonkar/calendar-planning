import json

def calculate_itinerary(vilnius_days, naples_days, vienna_days):
    # Calculate the number of days in each city
    vilnius_start_day = 1
    vilnius_end_day = vilnius_days
    naples_start_day = vilnius_end_day + 1
    naples_end_day = naples_days + naples_start_day - 1
    vienna_start_day = naples_end_day + 1
    vienna_end_day = vienna_days + vienna_start_day - 1

    # Create the itinerary
    itinerary = []
    if vilnius_days > 0:
        itinerary.append({"day_range": f"Day {vilnius_start_day}-{vilnius_end_day}", "place": "Vilnius"})
    if naples_days > 0:
        itinerary.append({"day_range": f"Day {naples_start_day}-{naples_end_day}", "place": "Naples"})
    if vienna_days > 0:
        itinerary.append({"day_range": f"Day {vienna_start_day}-{vienna_end_day}", "place": "Vienna"})

    return itinerary

def main():
    vilnius_days = 7
    naples_days = 5
    vienna_days = 7
    itinerary = calculate_itinerary(vilnius_days, naples_days, vienna_days)
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))

if __name__ == "__main__":
    main()