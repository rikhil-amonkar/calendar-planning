#!/usr/bin/env python3
import json

def plan_itinerary():
    # Total number of days
    total_days = 27

    # We have 10 cities with fixed duration requirements and event constraints.
    # We will schedule them along a timeline with the possibility of overlapping flight days.
    # If a flight is taken on a given day X, that day is counted for both the departure and arrival cities.
    #
    # Planned ordering and logic (each flight happens on the first day of the new segment so that the day is double counted):
    # 1. Santorini: Must spend 3 days.
    #    Let Santorini be days 1 to 3.
    #
    # 2. Flight from Santorini to Vienna on day 3 (so day3 counts as both Santorini and Vienna).
    #    Vienna: 4 days, must include the wedding event between day 3 and day 6; we assume the wedding is held, say, on day5.
    #    Schedule Vienna for days 3-6.
    #
    # 3. Flight from Vienna to Madrid on day 6 (day6 is both for Vienna and Madrid).
    #    Madrid: 2 days, and the annual show occurs between day6 and day7.
    #    Schedule Madrid for days 6-7.
    #
    # 4. Flight from Madrid to Seville on day 7 (day7 counts for both Madrid and Seville).
    #    Seville: 2 days, schedule days 7-8.
    #
    # 5. Flight from Seville to Valencia on day 8 (day8 counts for both Seville and Valencia).
    #    Valencia: 4 days, schedule days 8-11.
    #
    # 6. Flight from Valencia to Krakow on day 11 (day11 counts for both Valencia and Krakow).
    #    Krakow: 5 days, with a friends meeting between day11 and day15.
    #    Schedule Krakow for days 11-15.
    #
    # 7. Flight from Krakow to Frankfurt on day 15 (day15 counts for both Krakow and Frankfurt).
    #    Frankfurt: 4 days, schedule days 15-18.
    #
    # 8. Flight from Frankfurt to Bucharest on day 18 (day18 counts for both Frankfurt and Bucharest).
    #    Bucharest: 3 days, schedule days 18-20.
    #
    # 9. Flight from Bucharest to Riga on day 20 (day20 counts for both Bucharest and Riga).
    #    Riga: 4 days, with the conference meeting on day20 and day23.
    #    Schedule Riga for days 20-23.
    #
    # 10. Flight from Riga to Tallinn on day 23 (day23 counts for both Riga and Tallinn).
    #     Tallinn: 5 days, with the workshop occurring between day23 and day27.
    #     Schedule Tallinn for days 23-27.
    
    # We now construct the itinerary segments.
    itinerary = [
        {"day_range": "1-3", "place": "Santorini"},   # Santorini: days 1,2,3
        {"day_range": "3-6", "place": "Vienna"},       # Vienna: days 3,4,5,6. Wedding event between day3 and day6.
        {"day_range": "6-7", "place": "Madrid"},       # Madrid: days 6,7. Annual show on day6-7.
        {"day_range": "7-8", "place": "Seville"},      # Seville: days 7,8.
        {"day_range": "8-11", "place": "Valencia"},     # Valencia: days 8,9,10,11.
        {"day_range": "11-15", "place": "Krakow"},      # Krakow: days 11,12,13,14,15. Friends tour event within these days.
        {"day_range": "15-18", "place": "Frankfurt"},   # Frankfurt: days 15,16,17,18.
        {"day_range": "18-20", "place": "Bucharest"},   # Bucharest: days 18,19,20.
        {"day_range": "20-23", "place": "Riga"},        # Riga: days 20,21,22,23. Conference on day20 and day23.
        {"day_range": "23-27", "place": "Tallinn"}      # Tallinn: days 23,24,25,26,27. Workshop between day23 and day27.
    ]
    
    return itinerary

def main():
    itinerary = plan_itinerary()
    # Output the itinerary as JSON formatted dictionary list
    print(json.dumps(itinerary, indent=2))
    
if __name__ == "__main__":
    main()