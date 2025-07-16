# Process day_sequence to create itinerary with ranges and flight days
itinerary = []
n = len(day_sequence)
i = 0
while i < n:
    start_day, city = day_sequence[i]
    j = i
    while j < n and day_sequence[j][1] == city:
        j += 1
    end_day = day_sequence[j-1][0]
    # Add the stay entry
    if start_day == end_day:
        itinerary.append({"day_range": f"Day {start_day}", "place": city})
    else:
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    # Check if there's a next city
    if j < n:
        # The transition day is day_sequence[j][0] (the first day of the next city)
        transition_day = day_sequence[j][0]
        next_city = day_sequence[j][1]
        # Add departure and arrival entries
        itinerary.append({"day_range": f"Day {transition_day}", "place": city})
        itinerary.append({"day_range": f"Day {transition_day}", "place": next_city})
    i = j