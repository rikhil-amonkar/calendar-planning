else:
    # If we have more than 32 days, we need to adjust the last stay
    last_stay = itinerary.pop()
    last_days = int(last_stay["day_range"].split('-')[1].split(' ')[1])
    new_days = last_days + remaining_days
    itinerary.append({"day_range": f"Day {last_days - new_days + 1}-{last_days}", "place": last_stay["place"]})