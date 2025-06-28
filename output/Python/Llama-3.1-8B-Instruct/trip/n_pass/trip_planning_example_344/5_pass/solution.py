import json

def compute_itinerary(
    days_total,
    days_valencia,
    days_athens,
    days_naples,
    days_zurich,
    relatives_visit_start,
    relatives_visit_end,
    wedding_visit_start,
    wedding_visit_end,
    direct_flights
):
    # Initialize variables
    day = 1
    itinerary = []
    current_city = None

    # Visit Valencia
    for _ in range(days_valencia):
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Valencia"})
        day += 1
        current_city = "Valencia"

    # Visit Athens
    if current_city == "Valencia":
        itinerary.append({"day_range": f"Day {days_valencia}-{days_valencia}", "place": "Athens"})
        day += 1
        current_city = "Athens"

    for _ in range(days_athens):
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Athens"})
        day += 1

    # Visit Naples
    if current_city == "Athens":
        itinerary.append({"day_range": f"Day {days_valencia+days_athens}-{days_valencia+days_athens}", "place": "Naples"})
        day += 1
        current_city = "Naples"

    for _ in range(days_naples):
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Naples"})
        day += 1

    # Visit Zurich
    if current_city == "Naples":
        itinerary.append({"day_range": f"Day {days_valencia+days_athens+days_naples}-{days_valencia+days_athens+days_naples}", "place": "Zurich"})
        day += 1
        current_city = "Zurich"

    # Ensure Zurich leg covers remaining days
    remaining_days = days_total - day + 1
    for _ in range(remaining_days):
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Zurich"})
        day += 1

    # Adjust itinerary based on relatives and wedding visits
    if relatives_visit_start <= days_valencia and relatives_visit_end >= days_valencia:
        relatives_days = relatives_visit_end - relatives_visit_start + 1
        for i in range(days_valencia, days_valencia+relatives_days):
            itinerary[i]["day_range"] = f"Day {days_valencia}-{days_valencia+relatives_days-1}"
        itinerary[days_valencia]["place"] = "Athens"
        itinerary[days_valencia+relatives_days-1]["place"] = "Athens"
        days_valencia += relatives_days - 1
        days_athens -= relatives_days - 1

    if wedding_visit_start <= days_valencia + days_athens + days_naples and wedding_visit_end >= days_valencia + days_athens + days_naples:
        wedding_days = min(wedding_visit_end - wedding_visit_start + 1, days_total - days_valencia - days_athens - days_naples)
        for i in range(days_valencia+days_athens+days_naples, days_valencia+days_athens+days_naples+wedding_days):
            itinerary[i]["day_range"] = f"Day {days_valencia+days_athens+days_naples}-{days_valencia+days_athens+days_naples+wedding_days-1}"
        itinerary[days_valencia+days_athens+days_naples]["place"] = "Naples"
        itinerary[days_valencia+days_athens+days_naples+wedding_days-1]["place"] = "Naples"
        days_naples += wedding_days - 1

    # Adjust direct flights
    for i in range(len(itinerary)-1):
        if itinerary[i]["place"] == "Valencia" and itinerary[i+1]["place"] == "Athens":
            itinerary[i]["day_range"] = f"Day {days_valencia}-{days_valencia}"
            itinerary[i+1]["day_range"] = f"Day {days_valencia}-{days_valencia}"
        elif itinerary[i]["place"] == "Athens" and itinerary[i+1]["place"] == "Naples":
            itinerary[i]["day_range"] = f"Day {days_valencia+days_athens}-{days_valencia+days_athens}"
            itinerary[i+1]["day_range"] = f"Day {days_valencia+days_athens}-{days_valencia+days_athens}"
        elif itinerary[i]["place"] == "Naples" and itinerary[i+1]["place"] == "Zurich":
            itinerary[i]["day_range"] = f"Day {days_valencia+days_athens+days_naples}-{days_valencia+days_athens+days_naples}"
            itinerary[i+1]["day_range"] = f"Day {days_valencia+days_athens+days_naples}-{days_valencia+days_athens+days_naples}"
        elif itinerary[i]["place"] == "Zurich" and itinerary[i+1]["place"] == "Valencia":
            itinerary[i]["day_range"] = f"Day {days_valencia+days_athens+days_naples+days_zurich}-{days_valencia+days_athens+days_naples+days_zurich}"
            itinerary[i+1]["day_range"] = f"Day {days_valencia+days_athens+days_naples+days_zurich}-{days_valencia+days_athens+days_naples+days_zurich}"
        elif itinerary[i]["place"] == "Athens" and itinerary[i+1]["place"] == "Zurich":
            itinerary[i]["day_range"] = f"Day {days_valencia+days_athens}-{days_valencia+days_athens}"
            itinerary[i+1]["day_range"] = f"Day {days_valencia+days_athens}-{days_valencia+days_athens}"
        elif itinerary[i]["place"] == "Zurich" and itinerary[i+1]["place"] == "Athens":
            itinerary[i]["day_range"] = f"Day {days_valencia+days_athens+days_naples+days_zurich}-{days_valencia+days_athens+days_naples+days_zurich}"
            itinerary[i+1]["day_range"] = f"Day {days_valencia+days_athens+days_naples+days_zurich}-{days_valencia+days_athens+days_naples+days_zurich}"

    # Adjust days in Zurich to ensure 20 days in total
    days_in_zurich = days_total - days_valencia - days_athens - days_naples
    for i in range(days_valencia+days_athens+days_naples, days_total):
        itinerary[i]["day_range"] = f"Day {days_valencia+days_athens+days_naples}-{days_total-1}"
    days_zurich = days_in_zurich

    return {"itinerary": itinerary}

# Define input variables
days_total = 20
days_valencia = 6
days_athens = 6
days_naples = 5
days_zurich = 7  # This will be adjusted to ensure 20 days in total
relatives_visit_start = 1
relatives_visit_end = 6
wedding_visit_start = 16
wedding_visit_end = 20
direct_flights = {
    "Valencia": ["Athens", "Zurich"],
    "Athens": ["Naples", "Zurich"],
    "Naples": ["Zurich"],
    "Zurich": ["Valencia", "Athens"]
}

# Compute and output itinerary
itinerary = compute_itinerary(days_total, days_valencia, days_athens, days_naples, days_zurich, relatives_visit_start, relatives_visit_end, wedding_visit_start, wedding_visit_end, direct_flights)
print(json.dumps(itinerary, indent=4))