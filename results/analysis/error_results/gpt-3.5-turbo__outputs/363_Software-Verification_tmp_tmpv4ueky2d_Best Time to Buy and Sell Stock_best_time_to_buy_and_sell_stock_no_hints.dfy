
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{
    var min_price := 10001;
    max_profit := 0;
    
    var i := 0;
    while i < prices.Length
        invariant 0 <= i <= prices.Length
        invariant forall k :: 0 <= k < i ==> min_price <= prices[k]
        invariant max_profit >= 0
        invariant forall k :: 0 <= k < i ==> max_profit >= prices[k] - min_price
    {
        var price := prices[i];
        assert min_price <= price;
        if price < min_price
        {
            min_price := price;
        }
        assert forall k :: 0 <= k <= i ==> min_price <= prices[k];
        if price - min_price > max_profit {
            max_profit := price - min_price;
        }
        assert forall k :: 0 <= k <= i ==> max_profit >= prices[k] - min_price;

        i := i + 1;
    }
    assert forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i];
}
