import re

def validate_days(itinerary, required_days):
    # Initialize city_days with all required cities set to 0
    city_days = {city: 0 for city in required_days}

    for segment in itinerary:
        city = segment["place"]
        # Check if the city is in required_days
        if city not in city_days:
            return False

        day_range_str = segment["day_range"]

        # Extract all digits from the day_range string
        numbers = re.findall(r'\d+', day_range_str)
        if not numbers:
            # No valid days found; assume 0 days for this segment
            days = 0
        else:
            start_day = int(numbers[0])
            end_day = int(numbers[-1]) if len(numbers) >= 2 else start_day
            days = end_day - start_day + 1

        # Add the calculated days to the corresponding city
        city_days[city] += days

    # Compare the accumulated days to the required days
    return city_days == required_days