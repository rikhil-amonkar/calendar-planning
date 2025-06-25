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
    while day <= days_valencia:
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Valencia"})
        day += 1
        current_city = "Valencia"

    # Visit Athens
    if current_city == "Valencia":
        itinerary.append({"day_range": f"Day {days_valencia+1}-{days_valencia+1}", "place": "Athens"})
        day += 1
        current_city = "Athens"

    while day <= days_valencia + days_athens:
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Athens"})
        day += 1

    # Visit Naples
    if current_city == "Athens":
        itinerary.append({"day_range": f"Day {days_valencia+days_athens+1}-{days_valencia+days_athens+1}", "place": "Naples"})
        day += 1
        current_city = "Naples"

    while day <= days_valencia + days_athens + days_naples:
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Naples"})
        day += 1

    # Visit Zurich
    if current_city == "Naples":
        itinerary.append({"day_range": f"Day {days_valencia+days_athens+days_naples+1}-{days_valencia+days_athens+days_naples+1}", "place": "Zurich"})
        day += 1
        current_city = "Zurich"

    while day <= days_valencia + days_athens + days_naples + days_zurich:
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Zurich"})
        day += 1

    # Adjust itinerary based on relatives and wedding visits
    if relatives_visit_start <= days_valencia and relatives_visit_end >= days_valencia:
        relatives_days = relatives_visit_end - relatives_visit_start + 1
        itinerary[days_valencia] = {"day_range": f"Day {days_valencia}-{days_valencia+relatives_days-1}", "place": "Athens"}
        itinerary[days_valencia+relatives_days-1] = {"day_range": f"Day {days_valencia+relatives_days}-{days_valencia+relatives_days}", "place": "Athens"}
        for i in range(days_valencia, days_valencia+relatives_days):
            itinerary[i]["day_range"] = f"Day {days_valencia}-{days_valencia+relatives_days-1}"
        days_valencia += relatives_days - 1
        days_athens -= relatives_days - 1

    if wedding_visit_start <= days_valencia + days_athens + days_naples and wedding_visit_end >= days_valencia + days_athens + days_naples:
        wedding_days = wedding_visit_end - wedding_visit_start + 1
        itinerary[days_valencia+days_athens+days_naples] = {"day_range": f"Day {days_valencia+days_athens+days_naples}-{days_valencia+days_athens+days_naples+wedding_days-1}", "place": "Naples"}
        itinerary[days_valencia+days_athens+days_naples+wedding_days-1] = {"day_range": f"Day {days_valencia+days_athens+days_naples+wedding_days}-{days_valencia+days_athens+days_naples+wedding_days}", "place": "Naples"}
        for i in range(days_valencia+days_athens+days_naples, days_valencia+days_athens+days_naples+wedding_days):
            itinerary[i]["day_range"] = f"Day {days_valencia+days_athens+days_naples}-{days_valencia+days_athens+days_naples+wedding_days-1}"
        days_naples += wedding_days - 1

    # Adjust itinerary to fit remaining days
    while day <= days_total:
        itinerary.append({"day_range": f"Day {day}-{day}", "place": "Zurich"})
        day += 1

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

    return {"itinerary": itinerary}

# Define input variables
days_total = 20
days_valencia = 6
days_athens = 6
days_naples = 5
days_zurich = 6
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