import json

def plan_trip():
    total_days = 7
    madrid_days_needed = 4
    dublin_days_needed = 3
    tallinn_days_needed = 2
    tallinn_workshop_start = 6
    tallinn_workshop_end = 7
    
    # Direct flights graph
    direct_flights = {
        "Madrid": ["Dublin"],
        "Dublin": ["Madrid", "Tallinn"],
        "Tallinn": ["Dublin"]
    }
    
    # We'll brute-force search over possible day-by-day itineraries
    # Since only 7 days and 3 cities, search space is small.
    
    cities = ["Madrid", "Dublin", "Tallinn"]
    
    # Helper to check if move is valid
    def can_move(from_city, to_city):
        if from_city == to_city:
            return True
        return to_city in direct_flights[from_city]
    
    # Generate all possible sequences
    from itertools import product
    
    all_sequences = list(product(cities, repeat=total_days))
    
    valid_sequences = []
    
    for seq in all_sequences:
        # Check direct flights between consecutive cities
        valid_transition = True
        for i in range(total_days - 1):
            if not can_move(seq[i], seq[i+1]):
                valid_transition = False
                break
        if not valid_transition:
            continue
        
        # Count days per city
        madrid_count = sum(1 for city in seq if city == "Madrid")
        dublin_count = sum(1 for city in seq if city == "Dublin")
        tallinn_count = sum(1 for city in seq if city == "Tallinn")
        
        # Adjust for travel double-counting:
        # If seq[i] != seq[i+1], day i+1 counts for both seq[i] and seq[i+1]? Wait careful.
        # Actually, if you travel on day X from A to B, day X counts for both A and B.
        # In our sequence, seq[i] is city on day i+1 (1-based). Travel happens between days.
        # Let's define: day d (1-based) you are in seq[d-1].
        # Travel happens at end of day d to go to seq[d] for next day? No, travel happens during the day.
        # Better: If seq[d-1] != seq[d], then day d is spent partly in seq[d-1] and partly in seq[d],
        # so it counts for both cities.
        
        # Let's count properly:
        city_days = {"Madrid": 0, "Dublin": 0, "Tallinn": 0}
        for day_idx in range(total_days):
            city = seq[day_idx]
            city_days[city] += 1
            # If next day is different, this day also counts for next city
            if day_idx + 1 < total_days and seq[day_idx + 1] != city:
                city_days[seq[day_idx + 1]] += 1
        
        # Remove duplicates? Wait, we overcounted: day_idx already counted for current city,
        # then if next day different, we added next city for same day_idx again? That's wrong.
        # Let's redo: Each day is counted for all cities visited that day.
        # On day_idx (0-based = day 1), you start in seq[day_idx].
        # If seq[day_idx] != seq[day_idx+1], you travel during day_idx, so you visit both.
        # So day_idx counts for seq[day_idx] and seq[day_idx+1].
        # But careful with last day: only one city.
        
        # Simpler: mark for each day which cities are visited.
        city_days = {"Madrid": 0, "Dublin": 0, "Tallinn": 0}
        for day_idx in range(total_days):
            cities_visited_today = {seq[day_idx]}
            if day_idx + 1 < total_days and seq[day_idx] != seq[day_idx + 1]:
                cities_visited_today.add(seq[day_idx + 1])
            for c in cities_visited_today:
                city_days[c] += 1
        
        # Check totals
        if (city_days["Madrid"] == madrid_days_needed and
            city_days["Dublin"] == dublin_days_needed and
            city_days["Tallinn"] == tallinn_days_needed):
            # Check Tallinn workshop days (1-based days 6 and 7)
            if seq[5] == "Tallinn" and seq[6] == "Tallinn":  # indices 5 and 6 for days 6 and 7
                valid_sequences.append(seq)
    
    # Choose first valid sequence
    if valid_sequences:
        seq = valid_sequences[0]
        # Convert to itinerary with day ranges
        itinerary = []
        current_city = seq[0]
        start_day = 1
        for day in range(1, total_days):
            if seq[day] != current_city:
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": current_city
                })
                current_city = seq[day]
                start_day = day
        # Add last segment
        itinerary.append({
            "day_range": f"Day {start_day}-{total_days}",
            "place": current_city
        })
        
        # Merge consecutive same-city entries (just in case)
        merged_itinerary = []
        for item in itinerary:
            if merged_itinerary and merged_itinerary[-1]["place"] == item["place"]:
                # Merge ranges
                prev_range = merged_itinerary[-1]["day_range"]
                prev_end = int(prev_range.split("-")[1].replace("Day ", ""))
                new_start = int(item["day_range"].split("-")[0].replace("Day ", ""))
                if prev_end + 1 == new_start:
                    merged_itinerary[-1]["day_range"] = f"Day {prev_range.split('-')[0].replace('Day ', '')}-{item['day_range'].split('-')[1]}"
                else:
                    merged_itinerary.append(item)
            else:
                merged_itinerary.append(item)
        
        return {"itinerary": merged_itinerary}
    else:
        return {"itinerary": []}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, indent=2))