module Main where

import Data.Array
import Data.Array.ST
import Data.List (maximumBy, tails, foldl')
import Data.Ord (comparing)
import Control.Monad (forM_, when)
import Control.Monad.ST
import System.CPUTime
import Text.Printf
import Data.Time (getCurrentTime, diffUTCTime)
import System.Random (randomRIO)

-- | Тестовые случаи для LIS
testCases :: [(String, [Int], Int)]
testCases = [
    ("Базовый пример 1", [3, 10, 2, 1, 20], 3),
    ("Убывающая последовательность", [30, 20, 10], 1),
    ("Все равны", [2, 2, 2], 1),
    ("Возрастающая последовательность", [10, 20, 35, 80], 4),
    ("LeetCode пример 1", [10, 9, 2, 5, 3, 7, 101, 18], 4),
    ("LeetCode пример 2", [0, 1, 0, 3, 2, 3], 4),
    ("LeetCode пример 3", [7, 7, 7, 7, 7, 7, 7], 1),
    ("CSES пример", [7, 3, 5, 3, 6, 2, 9, 8], 4),
    ("Пример с отрицательными числами", [3, 4, -1, 0, 6, 2, 3], 4)
  ]

-- | Большой пример для демонстрации экспоненциальной сложности
bigDecreasingTestCase :: (String, [Int], Int)
bigDecreasingTestCase = ("Большая убывающая последовательность", [100,99..71], 1)

-- | Большой пример с LIS длиной примерно 20
bigZigzagTestCase :: (String, [Int], Int)
bigZigzagTestCase =
  ("Зигзаг с длинным LIS",
   [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11],
   7)

-- | Генерирует случайную последовательность заданной длины
generateRandomSequence :: Int -> IO [Int]
generateRandomSequence n = sequence [randomRIO (1, 1000) | _ <- [1..n]]

-- РЕАЛИЗАЦИЯ 1: Наивная рекурсия
-- =============================
-- | Наивная рекурсивная реализация LIS
-- | Для каждого элемента проверяем, можно ли начать с него новую последовательность,
-- | или продолжить предыдущую. Это приводит к экспоненциальному времени выполнения,
-- | так как одни и те же подзадачи решаются многократно.
-- | Сложность: O(2^n) по времени, O(n) по памяти для стека вызовов
naiveLIS :: Ord a => [a] -> Int
naiveLIS [] = 0
naiveLIS xs = maximum [lis i | i <- [0..length xs - 1]]
  where
    lis i = 1 + maximum (0 : [lis j | j <- [i+1..length xs - 1], xs !! i < xs !! j])

-- РЕАЛИЗАЦИЯ 2: Мемоизация с помощью ленивых массивов
-- ================================================
-- | LIS с использованием ленивых массивов для мемоизации
-- | Создаём двумерный массив, где lisMemo[i][j] - длина LIS от i до j.
-- | Благодаря ленивости Haskell, элементы массива вычисляются только при необходимости.
-- | Сложность: O(n^2) по времени, O(n^2) по памяти
lisWithMemo :: Ord a => [a] -> Int
lisWithMemo [] = 0
lisWithMemo xs = maximum [dp ! i | i <- [0..n]]
  where
    n = length xs - 1
    a = listArray (0, n) xs

    dp = array (0, n) [(i, lis i) | i <- [0..n]]

    lis i = 1 + maximum (0 : [dp ! j | j <- [0..i-1], a ! j < a ! i])

-- РЕАЛИЗАЦИЯ 3: Автоматическая мемоизация
-- ====================================
-- | Функция автоматической мемоизации с использованием массива
-- | Позволяет записать рекурсивное решение, но добавляет мемоизацию автоматически
-- | Сложность: O(n^2) по времени, O(n) по памяти
memo :: (Ix i) => (i, i) -> (i -> a) -> (i -> a)
memo bounds f = (!) table
  where table = array bounds [(i, f i) | i <- range bounds]

lisAutoMemo :: Ord a => [a] -> Int
lisAutoMemo [] = 0
lisAutoMemo xs = maximum [lis i | i <- [0..n]]
  where n = length xs - 1
        a = listArray (0, n) xs
        lis = memo (0, n) $ \i ->
          1 + maximum (0 : [lis j | j <- [0..i-1], a ! j < a ! i])

-- РЕАЛИЗАЦИЯ 4: Использование монады ST для изменяемых массивов
-- =======================================================
-- | LIS с использованием изменяемых массивов в монаде ST
-- | Это классический императивный подход с динамическим программированием,
-- | но реализованный в чистом функциональном стиле благодаря монаде ST.
-- | Сложность: O(n^2) по времени, O(n) по памяти
lisST :: [Int] -> Int  -- Здесь указываем конкретный тип Int вместо полиморфного
lisST [] = 0
lisST xs = runST $ do
  let n = length xs
  dp <- newArray (0, n-1) 1 :: ST s (STUArray s Int Int)

  forM_ [1..n-1] $ \i ->
    forM_ [0..i-1] $ \j -> do
      when (xs !! j < xs !! i) $ do  -- Используем !! вместо индексации массива
        dpJ <- readArray dp j
        dpI <- readArray dp i
        when (dpJ + 1 > dpI) $ writeArray dp i (dpJ + 1)

  maximum <$> mapM (readArray dp) [0..n-1]

-- РЕАЛИЗАЦИЯ 5: Использование ленивых списков
-- =======================================
-- | LIS с использованием ленивых списков
-- | Функциональный подход "снизу-вверх", накапливающий возможные последовательности.
-- | Благодаря ленивости, не все возможные подпоследовательности вычисляются.
-- | Сложность: теоретически O(2^n) в худшем случае, но на практике работает быстрее
lisLazyList :: Ord a => [a] -> Int
lisLazyList [] = 0
lisLazyList xs = maximum $ map length $ foldr f [[]] xs
  where f x acc = [x:ys | ys <- acc, null ys || x < head ys] ++ acc

-- | Бонусная реализация: O(n log n) алгоритм с использованием бинарного поиска
-- | Этот алгоритм гораздо эффективнее всех предыдущих для больших входных данных
-- | Сложность: O(n log n) по времени, O(n) по памяти
lisOptimal :: Ord a => [a] -> Int
lisOptimal [] = 0
lisOptimal xs = length $ foldl' insertElement [] xs
  where
    -- Вставка элемента в "хвост" последовательности
    insertElement [] x = [x]
    insertElement tail x
      | x > last tail = tail ++ [x]  -- Если x больше последнего, добавляем в конец
      | otherwise =
          let pos = binarySearch x tail
          in take pos tail ++ [x] ++ drop (pos + 1) tail

    -- Бинарный поиск для нахождения первого элемента >= x
    binarySearch x xs = bSearch 0 (length xs - 1)
      where
        bSearch lo hi
          | lo > hi = lo
          | xs !! mid < x = bSearch (mid + 1) hi
          | otherwise = bSearch lo (mid - 1)
          where mid = (lo + hi) `div` 2

-- | Функция для запуска тестов на конкретной реализации LIS
-- Изменяем сигнатуру функции, чтобы явно указать тип элементов массива
runTests :: ([Int] -> Int) -> String -> [(String, [Int], Int)] -> IO ()
runTests lisFunc implName tests = do
  putStrLn $ "=== Тестирование " ++ implName ++ " ==="
  mapM_ (\(name, input, expected) -> do
            start <- getCurrentTime
            let result = lisFunc input
            end <- getCurrentTime
            let timeDiff = diffUTCTime end start
            printf "%-30s: " name
            if result == expected
              then printf "ПРОШЕЛ (результат: %d, время: %.6f с)\n" result (realToFrac timeDiff :: Double)
              else printf "ОШИБКА! Ожидаемый результат: %d, полученный: %d\n" expected result
        ) tests
  putStrLn ""

-- | Главная функция
main :: IO ()
main = do
  -- Базовые тесты
  putStrLn "Запуск тестов на базовых примерах..."
  putStrLn "======================================"
  runTests naiveLIS "Наивная рекурсия" testCases
  runTests lisWithMemo "Ленивые массивы" testCases
  runTests lisAutoMemo "Автоматическая мемоизация" testCases
  runTests lisST "Монада ST" testCases
  runTests lisLazyList "Ленивые списки" testCases
  runTests lisOptimal "Оптимальный O(n log n)" testCases

  -- Тесты на больших примерах
  putStrLn "Запуск тестов на большом убывающем примере..."
  putStrLn "=============================================="
  putStrLn "Предупреждение: наивная рекурсия может работать очень долго!"
  runTests lisWithMemo "Ленивые массивы" [bigDecreasingTestCase]
  runTests lisAutoMemo "Автоматическая мемоизация" [bigDecreasingTestCase]
  runTests lisST "Монада ST" [bigDecreasingTestCase]
  runTests lisLazyList "Ленивые списки" [bigDecreasingTestCase]
  runTests lisOptimal "Оптимальный O(n log n)" [bigDecreasingTestCase]
  putStrLn "Наивная рекурсия пропущена для большого убывающего примера."

  putStrLn "Запуск тестов на большом зигзагообразном примере..."
  putStrLn "=================================================="
  runTests lisWithMemo "Ленивые массивы" [bigZigzagTestCase]
  runTests lisAutoMemo "Автоматическая мемоизация" [bigZigzagTestCase]
  runTests lisST "Монада ST" [bigZigzagTestCase]
  runTests lisLazyList "Ленивые списки" [bigZigzagTestCase]
  runTests lisOptimal "Оптимальный O(n log n)" [bigZigzagTestCase]
  putStrLn "Наивная рекурсия пропущена для большого зигзагообразного примера."

  -- Генерация и тестирование на большом случайном примере
  putStrLn "Генерация большого случайного примера (1000 элементов)..."
  randomSeq <- generateRandomSequence 1000
  let randomTestCase = ("Случайная последовательность (1000)", randomSeq, lisOptimal randomSeq)

  putStrLn "Запуск тестов на большом случайном примере..."
  putStrLn "============================================"
  runTests lisAutoMemo "Автоматическая мемоизация" [randomTestCase]
  runTests lisST "Монада ST" [randomTestCase]
  runTests lisOptimal "Оптимальный O(n log n)" [randomTestCase]
  putStrLn "Наивная рекурсия и некоторые другие методы пропущены для большого случайного примера."
