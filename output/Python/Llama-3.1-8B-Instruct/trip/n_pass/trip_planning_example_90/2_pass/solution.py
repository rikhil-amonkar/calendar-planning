import json

def calculate_itinerary(vilnius_days, naples_days, vienna_days):
    """
    Calculate the itinerary for a trip to Vilnius, Naples, and Vienna.

    Args:
        vilnius_days (int): Number of days spent in Vilnius.
        naples_days (int): Number of days spent in Naples.
        vienna_days (int): Number of days spent in Vienna.

    Returns:
        list: Itinerary for the trip.
    """
    # Calculate the total number of days
    total_days = vilnius_days + naples_days + vienna_days

    # Check if the total number of days matches the constraint
    if total_days!= 17:
        raise ValueError("The total number of days must be 17.")

    # Calculate the start day for each city
    vilnius_start_day = 1
    naples_start_day = vilnius_days + 1
    vienna_start_day = naples_start_day + naples_days

    # Create the itinerary
    itinerary = []
    if vilnius_days > 0:
        itinerary.append({"day_range": f"Day {vilnius_start_day}-{vilnius_start_day + vilnius_days - 1}", "place": "Vilnius"})
    if naples_days > 0:
        itinerary.append({"day_range": f"Day {naples_start_day}-{naples_start_day + naples_days - 1}", "place": "Naples"})
    if vienna_days > 0:
        itinerary.append({"day_range": f"Day {vienna_start_day}-{vienna_start_day + vienna_days - 1}", "place": "Vienna"})

    return itinerary

def main():
    vilnius_days = 7
    naples_days = 3
    vienna_days = 7
    itinerary = calculate_itinerary(vilnius_days, naples_days, vienna_days)
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))

if __name__ == "__main__":
    main()