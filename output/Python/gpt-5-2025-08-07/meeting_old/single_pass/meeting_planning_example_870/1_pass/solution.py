if __name__ == "__main__":
    result = compute_best_schedule()
    print(json.dumps(result, ensure_ascii=False))